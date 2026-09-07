//! Real-loan retirement witnesses. Dangling accesses are compiled for static
//! analysis only, never executed, and make no UB-free-input soundness claim.

use std::{
    collections::{BTreeMap, BTreeSet},
    panic::{AssertUnwindSafe, catch_unwind},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Local, Location, VarDebugInfoContents};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::LocalDefId;

use super::{RetirementConflict, RetirementReview};
use crate::{
    analyses::{
        borrow::ProvenanceOwner,
        borrow_ownership::{
            SlotKind, borrow_verify, crate_slots::CrateSlots, export, slot_key, slots::SlotId,
            solver::SlotRef, source_events::SourceRole,
        },
        liveness::MaybeLiveLocals,
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

struct Replay {
    function: LocalDefId,
    locals: BTreeMap<String, Local>,
    selected: BTreeMap<(String, u8), (SlotRef, String)>,
    free_points: Vec<Location>,
    live_at_free: FxHashMap<Location, FxHashSet<Local>>,
    export: export::BoExport,
    panicked: bool,
}

fn replay(code: &str, name: &str, selected: &[(&str, u8)]) -> Replay {
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
        let named: Vec<_> = functions
            .iter()
            .copied()
            .filter(|function| tcx.item_name(function.to_def_id()).as_str() == name)
            .collect();
        assert_eq!(named.len(), 1, "exact source function");
        let function = named[0];
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let mut debug = BTreeMap::<String, BTreeSet<Local>>::new();
        for info in &body.var_debug_info {
            if let VarDebugInfoContents::Place(place) = info.value
                && let Some(local) = place.as_local()
            {
                debug
                    .entry(info.name.to_string())
                    .or_default()
                    .insert(local);
            }
        }
        let locals: BTreeMap<_, _> = debug
            .into_iter()
            .map(|(name, locals)| {
                assert_eq!(locals.len(), 1, "unique debug binding {name}");
                (name, *locals.iter().next().unwrap())
            })
            .collect();
        let mut model = FxHashMap::default();
        for index in 0..slots.field_slots.len() {
            model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
        }
        for (&owner, universe) in &slots.fn_local_slots {
            for index in 0..universe.len() {
                model.insert(
                    SlotRef::Local(owner, SlotId::from_usize(index)),
                    SlotKind::Raw,
                );
            }
        }
        let selected: BTreeMap<_, _> = selected
            .iter()
            .map(|&(name, depth)| {
                let local = locals[name];
                assert!(
                    local.as_usize() > body.arg_count,
                    "Ref selection must be a local, not a parameter"
                );
                let id = slots.fn_local_slots[&function]
                    .slot_for_local_depth(local, depth)
                    .expect("actual selected local/depth");
                let slot = SlotRef::Local(function, id);
                assert_eq!(model.insert(slot, SlotKind::Ref), Some(SlotKind::Raw));
                (
                    (name.to_owned(), depth),
                    (
                        slot,
                        slot_key::local_key(tcx, function, local.as_usize(), depth),
                    ),
                )
            })
            .collect();
        assert_eq!(
            model
                .values()
                .filter(|&&kind| kind == SlotKind::Ref)
                .count(),
            selected.len()
        );
        let free_points: Vec<_> = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(block, data)| {
                let call = data.terminator().as_call(tcx)?;
                matches!(call.func, CallKind::LibC(name) if name.as_str() == "free").then_some(
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                )
            })
            .collect();
        let mut cursor = MaybeLiveLocals
            .iterate_to_fixpoint(tcx, &body, None)
            .into_results_cursor(&body);
        let mut live_at_free = FxHashMap::default();
        for &location in &free_points {
            cursor.seek_before_primary_effect(location);
            live_at_free.insert(location, cursor.get().iter().collect());
        }
        let (outcome, captured) = export::with_bo_export(|| {
            catch_unwind(AssertUnwindSafe(|| {
                borrow_verify::revalidate_replaying(
                    &program,
                    &slots,
                    |slot| model.get(&slot) == Some(&SlotKind::Ref),
                    |slot| model.get(&slot) == Some(&SlotKind::Raw),
                    false,
                )
            }))
        });
        let review = captured
            .source_retirement
            .as_ref()
            .expect("real retirement review must be exported");
        assert!(
            outcome.is_ok() || !review.unresolved.is_empty(),
            "only a recorded typed retirement decline can explain a caught diagnostic panic"
        );
        assert!(
            captured
                .entry_protection
                .as_ref()
                .expect("entry capture")
                .entries
                .is_empty(),
            "a virtual parameter protector must not satisfy this real-loan test"
        );
        Replay {
            function,
            locals,
            selected,
            free_points,
            live_at_free,
            export: captured,
            panicked: outcome.is_err(),
        }
    })
    .unwrap_or_else(|error| error.raise())
}

fn complete(replay: &Replay) -> &RetirementReview {
    let review = replay.export.source_retirement.as_ref().unwrap();
    assert!(
        !replay.panicked,
        "this real-loan fixture requires actual conflict coverage"
    );
    assert!(
        review.unresolved.is_empty(),
        "unexpected fixture coverage gap: {:?}",
        review.unresolved
    );
    review
}

fn original_loan<'a>(
    replay: &'a Replay,
    conflict: &RetirementConflict,
) -> &'a export::LoanIdentity {
    let loan = conflict.loan.as_ref().expect("real-loan identity");
    assert_eq!(conflict.entry, None, "no virtual entry substitute");
    let matching: Vec<_> = replay
        .export
        .loans
        .iter()
        .filter(|row| {
            row.key.fn_did == conflict.function
                && row.run_local_handle == loan.index
                && row.key.location == export::location_key(loan.reservation)
                && row.key.place == loan.borrowed
        })
        .collect();
    assert_eq!(
        matching.len(),
        1,
        "same-inference BorrowSet identity must exist independently in the complete loan export"
    );
    assert_eq!(matching[0].class, export::LoanClass::Existing);
    matching[0]
}

#[test]
fn e5_p_d_real_shared_copy_loan_conflicts_with_heap_free() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn copied(p: *const u8) -> u8 {
    let q: *const u8 = p;
    let before = *q;
    free(p as *mut u8);
    before + *q
}
"#;
    let replay = replay(CODE, "copied", &[("q", 0)]);
    let (target, key) = &replay.selected[&("q".to_owned(), 0)];
    let rows: Vec<_> = complete(&replay)
        .conflicts
        .iter()
        .filter(|row| {
            row.function == replay.function
                && row.source.role == SourceRole::Free
                && row.target == *target
                && row.loan.is_some()
        })
        .collect();
    assert!(
        !rows.is_empty(),
        "the actual live q loan must reach retirement conflict extraction"
    );
    for row in rows {
        assert_eq!(&row.target_key, key);
        original_loan(&replay, row);
    }
}

#[test]
fn e5_p_d_real_stack_loan_survives_until_storage_dead_conflict() {
    const CODE: &str = r#"
pub unsafe fn dangling() -> u8 {
    let q: *const u8;
    { let cell = 7u8; q = &cell as *const u8; }
    *q
}
"#;
    let replay = replay(CODE, "dangling", &[("q", 0)]);
    let (target, key) = &replay.selected[&("q".to_owned(), 0)];
    let cell = replay.locals["cell"];
    let rows: Vec<_> = complete(&replay)
        .conflicts
        .iter()
        .filter(|row| {
            row.function == replay.function
                && row.source.role == SourceRole::StorageDead
                && row.source.storage_local == Some(cell.as_u32())
                && row.target == *target
                && row.loan.is_some()
        })
        .collect();
    assert!(
        !rows.is_empty(),
        "StorageDead(cell) must conflict with the actual surviving q loan"
    );
    for row in rows {
        assert_eq!(&row.target_key, key);
        original_loan(&replay, row);
    }
}

#[test]
fn e5_p_d_a_prime_selects_live_inner_requirer_over_dead_raw_issuer() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn requiring(p: *const u8) -> u8 {
    let raw_issuer: *const u8 = p;
    let inner: *const u8 = raw_issuer;
    free(p as *mut u8);
    *inner
}
"#;
    let replay = replay(CODE, "requiring", &[("inner", 0)]);
    assert_eq!(replay.free_points.len(), 1);
    let free = replay.free_points[0];
    let issuer = replay.locals["raw_issuer"];
    let inner = replay.locals["inner"];
    assert!(
        !replay.live_at_free[&free].contains(&issuer),
        "the source issuer must actually be dead at free"
    );
    assert!(
        replay.live_at_free[&free].contains(&inner),
        "the Ref requirer must actually be live"
    );
    let (target, key) = &replay.selected[&("inner".to_owned(), 0)];
    let rows: Vec<_> = complete(&replay)
        .conflicts
        .iter()
        .filter(|row| {
            if row.source.role != SourceRole::Free || row.target != *target || row.loan.is_none() {
                return false;
            }
            let original = original_loan(&replay, row);
            original.key.borrower
                == export::BorrowerKind::Assign {
                    owner: export::OwnerKey::Local(issuer.as_u32()),
                }
        })
        .collect();
    assert!(
        !rows.is_empty(),
        "the raw issuer's real loan must survive through its distinct live Ref requirer"
    );
    for row in rows {
        assert_eq!(&row.target_key, key);
        let owners = &row.loan.as_ref().unwrap().owners;
        assert!(owners.contains(&ProvenanceOwner::Local(inner)));
        assert!(
            !owners.contains(&ProvenanceOwner::Local(issuer)),
            "A′ must not offer the dead Raw issuer"
        );
    }
}

#[test]
fn e5_p_d_nonparameter_inner_slot_cannot_vanish_through_depth_zero_owner() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn deep(pp: *mut *mut u8) -> u8 {
    let localpp: *mut *mut u8 = pp;
    let q = *localpp;
    free(q);
    *q
}
"#;
    let replay = replay(CODE, "deep", &[("localpp", 1)]);
    let review = replay.export.source_retirement.as_ref().unwrap();
    let (target, key) = &replay.selected[&("localpp".to_owned(), 1)];
    let repaired = review.conflicts.iter().any(|row| {
        row.function == replay.function
            && row.source.role == SourceRole::Free
            && row.target == *target
            && &row.target_key == key
            && row.loan.is_some()
    });
    let declined = review.unresolved.iter().any(|row| {
        row.function == Some(replay.function)
            && row
                .source
                .as_ref()
                .is_some_and(|source| source.role == SourceRole::Free)
            && row
                .location
                .is_some_and(|location| replay.free_points.contains(&location))
    });
    assert!(
        repaired || declined,
        "a relevant live inner Ref local requires exact-depth repair or a typed source-retirement decline"
    );
}
