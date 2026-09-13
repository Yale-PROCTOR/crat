//! Native pipeline coverage on tiny heman-shaped sources. These assert the
//! current missing-bundle hold; they do not inject Owning model bits or claim
//! that synthetic validator premises establish a native positive bundle.

use super::decision::{Decision, DegradeReason, box_facts::BoxPlanFailure};

pub(super) fn native_fixture_source(callee: &str, body: &str) -> String {
    format!(
        r#"
        #![allow(dead_code,unused_unsafe,unused_mut)]
        extern "C" {{
            fn calloc(count:usize,size:usize)->*mut core::ffi::c_void;
            fn free(ptr:*mut core::ffi::c_void);
        }}
        unsafe fn {callee}(input:*mut f32,output:*mut f32) {{ *output=*input+1.0; }}
        pub unsafe fn transform_to_coordfield()->f32 {{
            let mut pl1=calloc(2,core::mem::size_of::<f32>()) as *mut f32;
            let mut pl2=calloc(2,core::mem::size_of::<f32>()) as *mut f32;
            *pl1=3.0;
            {body}
            let result=*pl1+*pl2;
            free(pl1 as *mut core::ffi::c_void);
            free(pl2 as *mut core::ffi::c_void);
            result
        }}
        "#,
    )
}

fn check_native_hold(callee: &str, body: &str) {
    let source = native_fixture_source(callee, body);
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("actual native fixture analysis");
        let mut observed = 0;
        for (subject, decision) in &table.entries {
            if !matches!(subject.param_name.as_deref(), Some("pl1" | "pl2")) {
                continue;
            }
            let slot = ctx.slots.fn_local_slots[&subject.fn_did]
                .slot_for_local_depth(subject.local, 0)
                .unwrap();
            let kind = ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot));
            println!(
                "OWNFIELDS-NATIVE {callee} {} {kind:?} {decision:?}",
                subject.label
            );
            assert_eq!(
                kind,
                Some(&super::SlotKind::Owning),
                "real model premise, never injected"
            );
            match decision {
                Decision::Degraded(d) => match &d.reason {
                    DegradeReason::BoxFailure {
                        failure: BoxPlanFailure::NativeEvidenceHeld { detail, .. },
                    } => {
                        assert!(detail.contains("native-subject-bundle"));
                    }
                    other => panic!("expected exact missing native bundle, got {other:?}"),
                },
                other => panic!("a native positive needs actual bundle producers, got {other:?}"),
            }
            observed += 1;
        }
        assert_eq!(observed, 2, "both caller owners must be accounted for");
    })
    .expect("native source fixture compiles");
}

#[test]
fn owning_native_two_buffer_edt_reports_missing_bundle_without_fabricating_a_box() {
    check_native_hold("edt_with_payload", "edt_with_payload(pl1,pl2);");
}

#[test]
fn owning_native_transform_reports_missing_bundle_for_repeated_caller_live_calls() {
    check_native_hold("edt", "edt(pl1,pl2);*pl1=*pl2;edt(pl1,pl2);");
}
