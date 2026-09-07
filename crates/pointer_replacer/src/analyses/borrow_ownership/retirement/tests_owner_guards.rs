//! Guard faults applied to actual compiler-owned catalog entries. The source
//! has a live real loan across free; it is compiled only, never executed.

use std::collections::BTreeSet;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Local, Location, Operand, Rvalue, StatementKind, VarDebugInfoContents};

use super::{CURRENT, EventDisposition, UnresolvedReason, begin};
use crate::{
    analyses::{
        borrow::ProvenanceOwner,
        borrow_ownership::{
            borrow_engine::borrow_conflicts_with_flows,
            crate_slots::CrateSlots,
            export::{self, BorrowerKind, LoanClass, OwnerKey, PlaceKey, ProjKey},
            origin_flow::analyze_program_origin_flow,
            slot_key,
            solver::SlotRef,
            source_events::{SourcePhase, SourceRole},
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug)]
enum Fault {
    Owner,
    Key,
}

fn check(fault: Fault) {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn f(p: *const u8) -> u8 {
    let q: *const u8 = p;
    free(p as *mut u8);
    *q
}
"#;
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
        let matching: Vec<_> = functions
            .iter()
            .copied()
            .filter(|function| tcx.item_name(function.to_def_id()).as_str() == "f")
            .collect();
        assert_eq!(matching.len(), 1);
        let function = matching[0];
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let named = |name: &str| {
            let locals: BTreeSet<Local> = body
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
            assert_eq!(locals.len(), 1, "actual named binding {name}");
            *locals.iter().next().unwrap()
        };
        let p = named("p");
        let q = named("q");
        assert!(p.as_usize() > 0 && p.as_usize() <= body.arg_count);
        assert!(
            q.as_usize() > body.arg_count,
            "the sole Ref is not a parameter"
        );
        let mut reservations = Vec::new();
        let mut frees = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                if matches!(&statement.kind, StatementKind::Assign(box (destination,
                    Rvalue::Use(Operand::Copy(source) | Operand::Move(source))))
                    if destination.as_local() == Some(q) && source.as_local() == Some(p))
                {
                    reservations.push(Location {
                        block,
                        statement_index,
                    });
                }
            }
            if let Some(call) = data.terminator().as_call(tcx)
                && matches!(call.func, CallKind::LibC(name) if name.as_str() == "free")
            {
                frees.push(Location {
                    block,
                    statement_index: data.statements.len(),
                });
            }
        }
        assert_eq!(reservations.len(), 1, "actual q=p loan reservation");
        assert_eq!(frees.len(), 1, "original source free");
        let free = frees[0];
        let slots = CrateSlots::build(&program);
        let target = SlotRef::Local(
            function,
            slots.fn_local_slots[&function]
                .slot_for_local_depth(q, 0)
                .unwrap(),
        );
        let target_key = slot_key::local_key(tcx, function, q.as_usize(), 0);
        let flows = analyze_program_origin_flow(&program);
        let ((review, source), captured) = export::with_bo_export(|| {
            // No borrow_verify wrapper: it would replace this deliberately
            // faulted catalog with a newly constructed retirement scope.
            let scope = begin(&program, &slots, |slot| slot == target);
            let source = CURRENT.with(|current| {
                let mut current = current.borrow_mut();
                let context = current.as_mut().expect("manual retirement context");
                assert_eq!(context.refs.len(), 1);
                assert!(context.refs.contains(&target));
                assert!(
                    context.entries.entries.is_empty(),
                    "no virtual-parameter substitute"
                );
                match fault {
                    Fault::Owner => assert_eq!(
                        context
                            .locals
                            .remove(&(function, ProvenanceOwner::Local(q))),
                        Some(target)
                    ),
                    Fault::Key => {
                        assert_eq!(context.keys.remove(&target), Some(target_key.clone()))
                    }
                }
                context.source.clone()
            });
            let _ordinary = borrow_conflicts_with_flows(
                &program,
                &flows,
                |owner| move |local| owner == function && local == q,
                |_| |_| false,
            );
            // Ordinary errors may coexist; this unit asserts the independent
            // retirement catalog guard, not absence of the ordinary channel.
            (scope.finish(), source)
        });
        let real: Vec<_> = captured
            .loans
            .iter()
            .filter(|loan| {
                loan.key.fn_did == function
                    && loan.key.location == export::location_key(reservations[0])
                    && loan.key.place
                        == (PlaceKey {
                            local: p,
                            proj: vec![ProjKey::Deref],
                        })
                    && loan.key.borrower
                        == (BorrowerKind::Assign {
                            owner: OwnerKey::Local(q.as_u32()),
                        })
            })
            .collect();
        assert_eq!(
            real.len(),
            1,
            "the same native inference must export its actual q loan before any early exit"
        );
        assert_eq!(real[0].class, LoanClass::Existing);
        let keys: Vec<_> = source
            .retirements
            .keys()
            .filter(|key| {
                key.function == "f"
                    && key.role == SourceRole::Free
                    && key.phase == SourcePhase::Call
                    && key.block == free.block.as_u32()
                    && key.statement == free.statement_index
            })
            .collect();
        assert_eq!(keys.len(), 1);
        let source_key = keys[0];
        let rows: Vec<_> = review
            .unresolved
            .iter()
            .filter(|row| {
                row.source.as_ref() == Some(source_key)
                    && row.function == Some(function)
                    && row.location == Some(free)
                    && row.phase == Some(SourcePhase::Call)
                    && row.route.is_empty()
            })
            .collect();
        assert!(
            !rows.is_empty(),
            "the guard fault must remain a typed source-site failure"
        );
        assert!(
            rows.iter().any(|row| match (&row.reason, fault) {
                (
                    UnresolvedReason::MissingOwner {
                        loan,
                        owner: Some(ProvenanceOwner::Local(local)),
                    },
                    Fault::Owner,
                ) => *loan == real[0].run_local_handle && *local == q,
                (UnresolvedReason::MissingSlotKey(slot), Fault::Key) => *slot == target,
                _ => false,
            }),
            "exact actual-owner/key failure missing: {rows:?}"
        );
        assert!(
            review.targets().is_empty(),
            "a missing owner/key cannot become an invented Ref repair target"
        );
        assert!(review.conflicts.is_empty());
        assert_eq!(
            review.terminal.get(source_key),
            Some(&EventDisposition::Unresolved)
        );
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_p_d_missing_actual_real_loan_owner_fails_closed() {
    check(Fault::Owner);
}

#[test]
fn e5_p_d_missing_actual_real_loan_slot_key_fails_closed() {
    check(Fault::Key);
}
