//! J13 premise reads only. These tests report actual decisions and evidence;
//! they do not assert admission, render an adapter, or establish delivery.

use rustc_middle::mir::RETURN_PLACE;
use sha2::{Digest, Sha256};

use super::decision::Decision;

fn decision_record(decision: Option<&Decision>) -> serde_json::Value {
    let Some(decision) = decision else { return serde_json::json!({"observed": false}) };
    let hold = match decision {
        Decision::Degraded(record) => Some(serde_json::json!({
            "reason": record.reason.key(), "typed_reason": format!("{:?}", record.reason),
            "subject": record.subject, "site": record.site,
        })),
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_) => None,
    };
    serde_json::json!({"observed": true, "decision": format!("{decision:?}"),
        "form": super::decision::seam::form_of(decision).key(), "hold": hold})
}

fn observe(name: &'static str, source: &'static str) {
    let observation = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        // Exactly one ordinary fixture decision invocation. Everything below
        // reads its retained context; no analysis or model is recomputed.
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("premise fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-FAMILY-PREMISE {name} solve={solve:#?}");
        assert!(solve.is_some(), "the one fixture decision invocation must retain its solve receipt");
        let (subject, final_decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("original raw-pointer parameter is inventoried");
        let node = (subject.fn_did, subject.hir_id);
        let candidate = ctx.hypothetical.entries.iter().find(|(candidate, _)|
            (candidate.fn_did, candidate.hir_id) == node).map(|(_, decision)| decision);
        let slot = |local| ctx.slots.fn_local_slots.get(&subject.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(local, 0));
        let model = |local| slot(local).and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
            .map(|kind| format!("{kind:?}"));
        let body = tcx.mir_drops_elaborated_and_const_checked(subject.fn_did).borrow();
        let flow = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&subject.fn_did));
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        let parameter_to_return = flow.map(|flow| flow.body.depth0_value_flows().contains(&(
            SlotOwner::Local(subject.local), SlotOwner::Local(RETURN_PLACE))));
        let native_flows = flow.map(|flow| format!("{:?}", flow.body.depth0_value_flows()));
        let raw_uses = ctx.facts.raw_only_uses.get(&node).map(|uses| uses.iter().map(|(operation, span)| {
            serde_json::json!({"operation": operation, "span_lo": span.lo().0, "span_hi": span.hi().0})
        }).collect::<Vec<_>>());
        let null_tests = ctx.facts.raw_only_uses.get(&node).map(|uses| uses.iter()
            .filter(|(operation, _)| operation == "is_null")
            .map(|(_, span)| serde_json::json!({"span_lo": span.lo().0, "span_hi": span.hi().0}))
            .collect::<Vec<_>>());
        let permit = ctx.lifetime_eligibility.return_permit(node);
        let lifetime_failure = ctx.lifetime_eligibility.failure(node);
        let lifetime_plan = table.lifetime_plan.function(subject.fn_did).map(|plan| plan.receipt());
        serde_json::json!({
            "probe": name, "classification": "premise-read-not-an-adapter-witness",
            "source": source, "source_sha256": format!("{:x}", Sha256::digest(source.as_bytes())),
            "source_identity": subject.identity_key(&tcx.def_path_str(subject.fn_did.to_def_id())),
            "source_local": subject.local.as_u32(), "return_local": RETURN_PLACE.as_u32(),
            "source_slot": slot(subject.local).map(|slot| format!("{slot:?}")),
            "return_slot": slot(RETURN_PLACE).map(|slot| format!("{slot:?}")),
            "source_model_kind": model(subject.local), "return_model_kind": model(RETURN_PLACE),
            "source_input_type": format!("{:?}", body.local_decls[subject.local].ty),
            "return_input_type": format!("{:?}", body.local_decls[RETURN_PLACE].ty),
            "source_mutable": ctx.mut_facts.is_mutable(subject.fn_did, subject.local),
            "source_mutability_defaulted": ctx.mut_facts.is_defaulted(subject.fn_did, subject.local),
            "return_mutable": ctx.mut_facts.is_mutable(subject.fn_did, RETURN_PLACE),
            "return_mutability_defaulted": ctx.mut_facts.is_defaulted(subject.fn_did, RETURN_PLACE),
            "source_candidate": decision_record(candidate), "source_final": decision_record(Some(final_decision)),
            "raw_fatness": {"status": "unavailable-in-retained-DecideCtx", "value": serde_json::Value::Null},
            "raw_uses": raw_uses, "nullability_evidence": {"source_null_init": subject.null_init, "source_null_tests": null_tests},
            "native_parameter_to_return": parameter_to_return, "native_depth0_flows": native_flows,
            "return_permit_present": permit.is_some(), "return_permit": permit.map(|permit| format!("{permit:?}")),
            "lifetime_failure": lifetime_failure.map(|failure| format!("{failure:?}")),
            "return_lifetime_plan": lifetime_plan,
            "original_return_interface": table.input_interfaces.return_forms.get(&subject.fn_did).map(|form| form.key()),
            "e2_subject_receipts": ctx.e2_artifacts.subjects,
            "e2_failure_receipts": ctx.e2_artifacts.failures,
        })
    }).expect("original premise fixture type-checks");
    println!(
        "RETURN-FAMILY-PREMISE {}",
        serde_json::to_string_pretty(&observation).unwrap()
    );
}

#[test]
fn return_family_premise_nullable_mutable_parameter_return() {
    observe(
        "nullable-mutable-parameter-return",
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe fn target(p: *mut i32) -> *mut i32 {
            if !p.is_null() { *p += 1; }
            p
        }
        pub unsafe fn entry() -> i32 {
            let mut value = 3;
            let returned = target(&mut value);
            if !returned.is_null() { *returned += 1; }
            let absent = target(core::ptr::null_mut());
            if absent.is_null() { value } else { 0 }
        }
    "#,
    );
}

#[test]
fn return_family_premise_positive_offset_slice_parameter_return() {
    observe(
        "positive-offset-parameter-return",
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe fn target(p: *mut i32) -> *mut i32 {
            *p.offset(1) += 1;
            p.offset(1)
        }
        pub unsafe fn entry() -> i32 {
            let mut values = [3, 5, 7];
            let returned = target(values.as_mut_ptr());
            *returned += 1;
            values[1]
        }
    "#,
    );
}
