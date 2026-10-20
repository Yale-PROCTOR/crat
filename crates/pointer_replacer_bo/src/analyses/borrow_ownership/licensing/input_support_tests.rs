//! Conditional input-store support does not enable the pending native guard.
use super::{field_support, graph_tests::with_facts};
const CODE: &str = r#"
unsafe extern "C" { fn malloc(n:usize)->*mut core::ffi::c_void; fn free(p:*mut core::ffi::c_void); }
pub struct Cell { ptr:*mut i32 }
pub unsafe fn make()->*mut i32 { let p=malloc(4) as *mut i32; *p=5; p }
pub unsafe fn put(cell:*mut Cell,value:*mut i32) { (*cell).ptr=value; }
pub unsafe fn take(cell:*mut Cell)->*mut i32 { let p=(*cell).ptr; (*cell).ptr=0 as *mut i32; p }
pub unsafe fn release(cell:*mut Cell) { let p=take(cell); free(p as *mut core::ffi::c_void); }
pub unsafe fn f() { let owner=make(); let mut cell=Cell{ptr:0 as *mut i32}; put(&mut cell,owner); release(&mut cell); }
"#;

fn proof(facts: &super::facts::Facts) -> field_support::FieldProof {
    let frozen = facts.licensing.as_ref().unwrap();
    field_support::audit(
        facts,
        &facts.field_support_inputs,
        &frozen.matched,
        &frozen.value_origins,
    )
    .into_iter()
    .find(|p| p.field_key == "Cell::field0@d0")
    .unwrap()
}

#[test]
fn c03_input_support_records_conditional_ol06_forwarding_without_permission() {
    with_facts(CODE, |facts| {
        let field = proof(facts);
        assert_eq!(
            field.input_stores.len(),
            1,
            "symbolic put store must retain conditional caller support"
        );
        let store = &field.input_stores[0];
        assert_eq!(
            store.caller_coverage,
            field_support::CallerCoverage::PendingCompilerAndAttestation
        );
        assert_eq!(store.applications.len(), 1);
        let call = &store.applications[0];
        assert_eq!(call.application.call.callee, "put");
        assert!(
            !call.alternatives.is_empty(),
            "exact source→original-cell→free alternative"
        );
        for route in &call.alternatives {
            assert_eq!(route.forwarded.actual, route.route.actual_output);
            assert_eq!(route.forwarded.formal, route.route.formal_output);
            assert_eq!(route.forwarded.output.source, route.free.source);
            assert!(matches!(
                route.free.terminal.target,
                super::matched::TerminalTarget::Free(_)
            ));
        }
        assert!(
            field.stores.is_empty(),
            "conditional input stores must not masquerade as C05 direct initializers"
        );
    });
}

#[test]
fn c03_input_support_keeps_stack_caller_and_partner_free_held() {
    for (code, reason) in [
        (
            format!(
                "{CODE}\npub unsafe fn other()->i32 {{ let mut x=9; let p=&mut x as *mut i32; let mut c=Cell{{ptr:0 as *mut i32}}; put(&mut c,p); let q=take(&mut c); *q }}"
            ),
            field_support::Pending::OwnedInputOrOriginC,
        ),
        (
            CODE.replace(
                "release(&mut cell);",
                "release(&mut cell); free(owner as *mut core::ffi::c_void);",
            ),
            field_support::Pending::CompetingTerminal,
        ),
    ] {
        with_facts(&code, move |facts| {
            let field = proof(facts);
            assert_eq!(
                field.input_stores.len(),
                1,
                "retain the attempted symbolic store and its caller roster"
            );
            assert!(!field.supported());
            assert!(field.holds.iter().any(|h| h.reason == reason), "{field:#?}");
            if reason == field_support::Pending::OwnedInputOrOriginC {
                assert_eq!(field.input_stores[0].applications.len(), 2);
                assert!(
                    field.input_stores[0]
                        .applications
                        .iter()
                        .any(|c| c.application.call.caller == "other" && c.alternatives.is_empty())
                );
            }
        });
    }
}

#[test]
fn c03_input_support_missing_caller_correspondence_is_not_omitted() {
    with_facts(CODE, |facts| {
        let baseline = proof(facts);
        assert_eq!(baseline.input_stores.len(), 1);
        let frozen = facts.licensing.as_ref().unwrap();
        let mut missing = facts.clone();
        missing
            .boundary_substitutions
            .retain(|b| b.callee.as_deref() != Some("put"));
        let matched = super::matched::MatchedTransport::build_metadata(
            &missing,
            frozen.matched.guard_aliases(),
        )
        .unwrap();
        let field = field_support::audit(
            &missing,
            &missing.field_support_inputs,
            &matched,
            &frozen.value_origins,
        )
        .into_iter()
        .find(|p| p.field_key == "Cell::field0@d0")
        .unwrap();
        assert_eq!(field.input_stores[0].applications.len(), 1);
        assert!(
            field.input_stores[0].applications[0]
                .alternatives
                .is_empty()
        );
        assert!(!field.supported());
    });
}
