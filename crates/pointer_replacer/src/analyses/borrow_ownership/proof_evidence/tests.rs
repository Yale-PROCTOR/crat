//! Compile-only evidence fixtures: actual source facts, never unsafe execution.
use rustc_hir::{ItemKind, OwnerNode};

use super::*;
use crate::{
    analyses::borrow_ownership::{
        crate_slots::CrateSlots, export, protected_entry, slots::SlotOwner, solver::SlotRef,
        source_events,
    },
    utils::rustc::RustProgram,
};
fn fixture(code: &str, check: impl FnOnce(ProofEvidence) + Send + Sync) {
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
        let (_, captured) = export::with_bo_export(|| {
            let inventory = source_events::for_construction(&program);
            export::record(|e| e.source_events = Some(inventory));
            let _entry = protected_entry::for_model(&program, &slots, |slot| {
                let SlotRef::Local(did, id) = slot else { return false };
                let descriptor = slots.fn_local_slots[&did].slot(id);
                let SlotOwner::Local(local) = descriptor.owner else { return false };
                let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                local.as_usize() > 0 && local.as_usize() <= body.arg_count
            });
        });
        check(ProofEvidence::from_export(tcx, &captured));
    })
    .unwrap_or_else(|error| error.raise());
}
fn rows(e: &ProofEvidence, f: Family) -> &[Row] {
    e.families[&f].as_deref().expect("actual capture family")
}
const CODE: &str = r#"
pub struct H { pub p:*const u8 }
unsafe extern "C" { fn free(p:*mut u8); }
pub unsafe fn f(mut p:*const u8, pp:*const *const u8, h:*mut H, again:bool) {
 let copied=p; (*h).p=copied;
 while again { let q=*pp; let _=q; }
 p=core::ptr::null(); let _=copied; let _=p; free(copied as *mut u8);
}
"#;
#[test]
fn e5_sched_source_facts_do_not_become_emitted_history_proof() {
    fixture(CODE, |e| {
        assert!(!rows(&e, Family::SourceRetirement).is_empty());
        assert!(!rows(&e, Family::Entry).is_empty());
        assert!(!rows(&e, Family::Observation).is_empty());
        assert!(e.missing.contains(&Missing::EmittedSchedule));
        assert!(e.licensing_deferred);
        assert_eq!(e.claim, Claim::SourceObservationsOnly);
        e.validate().unwrap();
        let json = e.canonical_json().unwrap();
        assert_eq!(serde_json::from_str::<ProofEvidence>(&json).unwrap(), e);
    });
}
#[test]
fn e5_kill_copied_stored_loop_and_deeper_facts_keep_missing_coverage() {
    fixture(CODE, |e| {
        assert!(
            rows(&e, Family::Entry)
                .iter()
                .any(|r| r.key.contains("@d1"))
        );
        assert!(!rows(&e, Family::Binding).is_empty());
        assert!(!rows(&e, Family::Witness).is_empty());
        assert!(
            rows(&e, Family::Observation)
                .iter()
                .any(|r| r.facts.get("moment").is_some_and(|s| s == "AfterExit"))
        );
        assert!(e.missing.contains(&Missing::GeneralKillSurvival));
        assert!(e.missing.contains(&Missing::DynamicAllocationEpoch));
        assert!(e.missing.contains(&Missing::CompleteDescendantAncestry));
    });
}
#[test]
fn e5_t16_unknown_target_alternatives_remain_unadmitted() {
    fixture(
        "pub unsafe fn f(p:*mut u8,call:unsafe fn(*mut u8)){call(p);}",
        |e| {
            assert!(
                rows(&e, Family::CallTargets)
                    .iter()
                    .any(|r| r.facts.get("unknown").is_some_and(|s| s == "true"))
            );
            assert!(e.missing.contains(&Missing::T16TighterFootprint));
            assert!(e.missing.contains(&Missing::T16AllHistories));
            let mut forged = e.clone();
            forged.missing.remove(&Missing::T16AllHistories);
            assert!(forged.validate().is_err());
        },
    );
}
#[test]
fn e5_proof_schema_rejects_duplicate_dangling_and_claim_promotion() {
    fixture(CODE, |e| {
        let entry = rows(&e, Family::Entry)[0].clone();
        let mut duplicate = e.clone();
        duplicate
            .families
            .get_mut(&Family::Entry)
            .unwrap()
            .as_mut()
            .unwrap()
            .push(entry);
        assert!(duplicate.validate().is_err());
        let mut dangling = e.clone();
        dangling
            .families
            .get_mut(&Family::Observation)
            .unwrap()
            .as_mut()
            .unwrap()[0]
            .references
            .push("missing-entry".into());
        assert!(dangling.validate().is_err());
        let mut licensing = e.clone();
        licensing.licensing_deferred = false;
        assert!(licensing.validate().is_err());
        let mut schedule = e.clone();
        schedule.missing.remove(&Missing::EmittedSchedule);
        assert!(schedule.validate().is_err());
    });
}
#[test]
fn e5_proof_absent_capture_is_missing_and_never_a_positive_empty_proof() {
    let e = ProofEvidence::default();
    assert!(e.families.values().all(Option::is_none));
    e.validate().unwrap();
    let mut forged = e.clone();
    forged.missing.clear();
    assert!(forged.validate().is_err());
}
