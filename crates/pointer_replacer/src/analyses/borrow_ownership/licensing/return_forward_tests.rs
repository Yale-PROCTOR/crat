//! Exact owning-return forwarding, without queries or permission changes.
use super::{
    facts::Facts,
    graph_tests::with_facts,
    matched::{Meet, SourceLineage, TerminalTarget},
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

#[test]
fn c04_return_forward_exact_take_exit_receiver_and_continuation() {
    with_facts(CODE, |facts| {
        let matched = &facts.licensing.as_ref().unwrap().matched;
        let (output, free) = pair(facts);
        let proof = matched
            .forward_return(facts, &output, &free)
            .expect("owning return is forwarded, not zeroed");
        assert_eq!(proof.output, output);
        assert_eq!(proof.continuation, free);
        assert_eq!(proof.call.caller, "release");
        assert_eq!(proof.call.callee, "take");
        assert_eq!(
            proof
                .call_path
                .iter()
                .map(|c| (&*c.caller, &*c.callee))
                .collect::<Vec<_>>(),
            vec![("f", "release"), ("release", "take")]
        );
        let equation = |id: super::facts::EquationId| {
            facts
                .equations
                .iter()
                .find(|e| e.point.construction == id.construction && e.ordinal == id.ordinal)
                .unwrap()
        };
        assert_eq!(
            equation(proof.exit_equation).variables,
            [proof.returned.var, proof.formal.var]
        );
        assert_eq!(
            equation(proof.receiver_equation).variables,
            [proof.receiver.var, proof.formal.var]
        );
        assert_eq!(
            equation(proof.receiver_old_zero).variables,
            [proof.receiver_old.var]
        );
        assert_eq!(equation(proof.receiver_old_zero).value, Some(false));
        assert!(
            facts
                .boundary_substitutions
                .iter()
                .any(|b| b.point.construction == proof.call.construction
                    && b.ordinal == proof.receiver_boundary
                    && b.actual_occurrence
                        == super::super::ownership_occurrence::Availability::Present(
                            proof.receiver_consume
                        ))
        );
        for (key, value) in output.guards.iter().chain(free.guards.iter()) {
            assert_eq!(proof.guards.get(key), Some(value));
        }
        let field = facts
            .licensing
            .as_ref()
            .unwrap()
            .field_support
            .iter()
            .find(|p| p.field_key == "Cell::field0@d0")
            .unwrap();
        assert!(
            !field.supported(),
            "compiler caller coverage remains pending"
        );
        assert!(
            matched.forward_return(facts, &free, &free).is_none(),
            "a free is never a return output"
        );
    });
}

#[test]
fn c04_return_forward_integrates_only_the_certified_pending_output() {
    with_facts(CODE, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let (output, free) = pair(facts);
        let certificate = frozen
            .matched
            .forward_return(facts, &output, &free)
            .unwrap();
        let field = frozen
            .field_support
            .iter()
            .find(|p| p.field_key == "Cell::field0@d0")
            .unwrap();
        let alternative = &field.input_stores[0].applications[0].alternatives[0];
        assert!(
            alternative.forwarded_returns.contains(&certificate),
            "persist the exact forwarding receipt"
        );
        assert!(
            !alternative.pending_outputs.contains(&output.terminal),
            "only the certified return output is closed"
        );
        assert!(
            alternative.route.source_terminals.contains(&output),
            "raw output evidence is retained"
        );
        assert_eq!(alternative.free, free, "the original free is retained");
        assert!(
            !field.supported(),
            "caller coverage and permission remain held"
        );
    });
}

#[test]
fn c04_return_forward_rejects_other_call_receiver_and_missing_equality() {
    with_facts(CODE, |facts| {
        let matched = &facts.licensing.as_ref().unwrap().matched;
        let (output, free) = pair(facts);
        let proof = matched
            .forward_return(facts, &output, &free)
            .expect("baseline certificate");
        let mut other = output.clone();
        let SourceLineage::Exact(calls) = &mut other.terminal.lineage else {
            panic!("exact lineage")
        };
        calls.last_mut().unwrap().statement += 1;
        assert!(matched.forward_return(facts, &other, &free).is_none());
        let mut missing = facts.clone();
        missing.equations.retain(|e| {
            e.point.construction != proof.exit_equation.construction
                || e.ordinal != proof.exit_equation.ordinal
        });
        assert!(matched.forward_return(&missing, &output, &free).is_none());
        let mut wrong = facts.clone();
        let boundary = wrong
            .boundary_substitutions
            .iter_mut()
            .find(|b| {
                b.point.construction == proof.call.construction
                    && b.ordinal == proof.receiver_boundary
            })
            .unwrap();
        boundary.actual_occurrence =
            super::super::ownership_occurrence::Availability::Present(usize::MAX);
        assert!(matched.forward_return(&wrong, &output, &free).is_none());
        let mut source = free.clone();
        source.source.endpoint = proof.exit_equation;
        assert!(matched.forward_return(facts, &output, &source).is_none());
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
