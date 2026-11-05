//! Exact owning-return forwarding, without queries or permission changes.
use super::{
    facts::Facts,
    graph_tests::with_facts,
    matched::{Meet, TerminalTarget},
};
const CODE: &str = r#"
unsafe extern "C" { fn malloc(n:usize)->*mut core::ffi::c_void; fn free(p:*mut core::ffi::c_void); }
pub struct Cell {ptr:*mut i32}
pub unsafe fn make()->*mut i32 {let p=malloc(4) as *mut i32; *p=5; p}
pub unsafe fn put(c:*mut Cell,p:*mut i32) {(*c).ptr=p;}
pub unsafe fn take(c:*mut Cell)->*mut i32 {let p=(*c).ptr; (*c).ptr=0 as *mut i32; p}
pub unsafe fn release(c:*mut Cell) {let p=take(c); free(p as *mut core::ffi::c_void);}
pub unsafe fn f() {let owner=make(); let mut c=Cell{ptr:0 as *mut i32}; put(&mut c,owner); release(&mut c);}
"#;

fn pair(facts: &Facts) -> (Meet, Meet) {
    let frozen = facts.licensing.as_ref().unwrap();
    let field = frozen
        .field_support
        .iter()
        .find(|p| p.field_key == "Cell::field0@d0")
        .unwrap();
    let alternative = &field.input_stores[0].applications[0].alternatives[0];
    let output = alternative
        .route
        .source_terminals
        .iter()
        .find(|meet| {
            let TerminalTarget::Output { node, ordinal } = meet.terminal.target else {
                return false;
            };
            facts.terminals.iter().any(|t| {
                t.point.construction == node.construction
                    && t.ordinal == ordinal
                    && t.point.function.as_deref() == Some("take")
                    && t.role == "return-output"
            })
        })
        .expect("take owning-return output stays visible");
    (output.clone(), alternative.free.clone())
}

/// Under the lend `take`'s owning-return output is not forwarded to `release`'s free.
#[test]
fn c04_return_forward_take_output_is_not_forwarded_under_the_lend() {
    with_facts(CODE, |facts| {
        let matched = &facts.licensing.as_ref().unwrap().matched;
        let (output, free) = pair(facts);
        assert!(matched.forward_return(facts, &output, &free).is_none());
    });
}

/// Under the lend no forwarding receipt is persisted and the output stays pending.
#[test]
fn c04_return_forward_persists_no_receipt_under_the_lend() {
    with_facts(CODE, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let (output, _) = pair(facts);
        let field = frozen
            .field_support
            .iter()
            .find(|p| p.field_key == "Cell::field0@d0")
            .unwrap();
        let alternative = &field.input_stores[0].applications[0].alternatives[0];
        assert!(alternative.forwarded_returns.is_empty());
        assert!(alternative.pending_outputs.contains(&output.terminal));
    });
}

/// Under the lend there is no baseline forwarding certificate to perturb.
#[test]
fn c04_return_forward_has_no_baseline_certificate_under_the_lend() {
    with_facts(CODE, |facts| {
        let matched = &facts.licensing.as_ref().unwrap().matched;
        let (output, free) = pair(facts);
        assert!(matched.forward_return(facts, &output, &free).is_none());
    });
}

#[test]
fn c04_return_forward_does_not_use_an_unrelated_partner_free() {
    let code = CODE.replace(
        "release(&mut c);",
        "release(&mut c); free(owner as *mut core::ffi::c_void);",
    );
    with_facts(&code, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let store = facts
            .equations
            .iter()
            .find(|e| {
                e.point.function.as_deref() == Some("put")
                    && e.operation == "equal"
                    && e.transfer.is_some()
            })
            .unwrap();
        let apps = frozen.matched.input_store_applications(
            facts,
            super::facts::EquationId {
                construction: store.point.construction,
                ordinal: store.ordinal,
            },
        );
        let route=apps[0].routes.iter().find(|r|!r.anchors.is_empty() && r.source_terminals.iter().any(|m|
            matches!(m.terminal.target,TerminalTarget::Output{node,ordinal} if facts.terminals.iter().any(|t|t.point.construction==node.construction && t.ordinal==ordinal && t.point.function.as_deref()==Some("take") && t.role=="return-output")))).unwrap();
        let output=route.source_terminals.iter().find(|m|matches!(m.terminal.target,TerminalTarget::Output{node,ordinal}
            if facts.terminals.iter().any(|t|t.point.construction==node.construction && t.ordinal==ordinal && t.point.function.as_deref()==Some("take") && t.role=="return-output"))).unwrap();
        let partner=route.source_terminals.iter().find(|m|matches!(m.terminal.target,TerminalTarget::Free(id)
            if facts.equations.iter().any(|e|e.point.construction==id.construction && e.ordinal==id.ordinal && e.point.function.as_deref()==Some("f")))).unwrap();
        assert!(
            frozen
                .matched
                .forward_return(facts, output, partner)
                .is_none()
        );
    });
}
