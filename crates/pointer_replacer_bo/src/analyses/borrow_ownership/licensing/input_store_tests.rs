//! Symbolic input/store applications, constructed without solver queries.
use super::{
    facts::{EquationId, Facts},
    graph_tests::with_facts,
    matched::{InputStoreStatus, MatchedTransport, TerminalTarget},
    transport::Node,
    value_origins::OriginAtom,
};

const OL06: &str = r#"
unsafe extern "C" { fn malloc(size: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
pub struct Cell { ptr: *mut i32 }
pub unsafe fn make() -> *mut i32 { let value=malloc(core::mem::size_of::<i32>()) as *mut i32; *value=5; value }
pub unsafe fn put(cell: *mut Cell, value: *mut i32) { (*cell).ptr=value; }
pub unsafe fn take(cell: *mut Cell) -> *mut i32 { let value=(*cell).ptr; (*cell).ptr=0 as *mut i32; value }
pub unsafe fn release(cell: *mut Cell) { let value=take(cell); free(value as *mut core::ffi::c_void); }
pub unsafe fn f() { let owner=make(); let mut cell=Cell { ptr:0 as *mut i32 }; put(&mut cell,owner); release(&mut cell); }
"#;

fn store(facts: &Facts) -> EquationId {
    let rows: Vec<_> = facts.equations.iter().filter(|row| row.point.function.as_deref()==Some("put")
        && row.operation=="equal" && row.transfer.as_ref().is_some_and(|transfer| {
            matches!(&transfer.destination, super::super::ownership_occurrence::Availability::Present(binding)
                if binding.path.iter().any(|step| matches!(step, super::super::ownership_occurrence::PathStep::Field { structure, .. } if structure=="Cell")))
        })).collect();
    assert_eq!(rows.len(), 1);
    EquationId {
        construction: rows[0].point.construction,
        ordinal: rows[0].ordinal,
    }
}

#[test]
fn c03_input_store_exact_put_application_keeps_symbolic_input_and_free() {
    with_facts(OL06, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let id = store(facts);
        let apps = frozen.matched.input_store_applications(facts, id);
        assert_eq!(
            apps.len(),
            1,
            "one expected put call, including missing applications"
        );
        assert_eq!(apps[0].status, InputStoreStatus::Observed);
        let cell = super::cell_effects::discover(facts)
            .into_iter()
            .find(|c| c.call.callee == "put")
            .unwrap();
        assert_eq!(apps[0].call, cell.call);
        let boundary = facts
            .boundary_substitutions
            .iter()
            .find(|b| b.point.construction == id.construction && b.ordinal == cell.boundary)
            .unwrap();
        let arm =
            super::cell_effects::call_arm(facts, boundary, frozen.matched.guard_aliases()).unwrap();
        let route = apps[0]
            .routes
            .iter()
            .find(|r| r.actual_output.var == arm.original.1)
            .expect("original cell output route");
        assert_eq!(route.guards.get(&arm.guard), Some(&true));
        assert_eq!(route.output_boundary, cell.boundary);
        assert!(!route.anchors.is_empty());
        let json = serde_json::to_value(route).unwrap();
        assert!(
            json["store_witness"]
                .as_array()
                .unwrap()
                .iter()
                .any(|step| *step == serde_json::json!({"Local":{"Transfer":id}})),
            "retained exact store step"
        );
        let free = facts
            .equations
            .iter()
            .find(|e| e.point.function.as_deref() == Some("release") && e.operation == "sink")
            .unwrap();
        let free = EquationId {
            construction: free.point.construction,
            ordinal: free.ordinal,
        };
        assert!(route.meets.iter().any(|meet| {
            meet.terminal.target == TerminalTarget::Free(free)
                && route
                    .anchors
                    .iter()
                    .any(|anchor| anchor.source == meet.source)
        }));
        let equation = facts
            .equations
            .iter()
            .find(|e| e.point.construction == id.construction && e.ordinal == id.ordinal)
            .unwrap();
        let node = Node {
            construction: id.construction,
            var: equation.transfer.as_ref().unwrap().source_use,
        };
        assert!(
            frozen
                .value_origins
                .at(node)
                .iter()
                .any(|atom| matches!(atom, OriginAtom::Input(_))),
            "the callee's symbolic origin is retained"
        );
        assert_eq!(
            frozen.matched.input_store_applications(facts, id),
            apps,
            "deterministic read-only application enumeration"
        );
    });
}

#[test]
fn c03_input_store_keeps_unanchored_second_object_and_missing_caller_rows() {
    let code = format!(
        "{OL06}\npub unsafe fn other()->i32 {{ let mut stack=9; let p=&mut stack as *mut i32; let mut cell=Cell {{ptr:0 as *mut i32}}; put(&mut cell,p); let q=take(&mut cell); *q }}"
    );
    with_facts(&code, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let id = store(facts);
        let apps = frozen.matched.input_store_applications(facts, id);
        assert_eq!(apps.len(), 2, "neither caller may disappear");
        let heap = apps.iter().find(|a| a.call.caller == "f").unwrap();
        let stack = apps.iter().find(|a| a.call.caller == "other").unwrap();
        assert!(heap.routes.iter().any(|r| !r.anchors.is_empty()));
        assert!(
            !stack.routes.is_empty(),
            "the pointer actual is represented despite lacking an allocation source"
        );
        assert!(
            stack
                .routes
                .iter()
                .all(|r| r.anchors.is_empty() && r.meets.is_empty())
        );
        let mut missing = facts.clone();
        missing.boundary_substitutions.retain(|row| {
            row.callee.as_deref() != Some("put") || row.point.function.as_deref() != Some("other")
        });
        let rebuilt =
            MatchedTransport::build_metadata(&missing, frozen.matched.guard_aliases()).unwrap();
        let missing = rebuilt.input_store_applications(&missing, id);
        let missing = missing
            .iter()
            .find(|a| a.call.caller == "other")
            .expect("original source call still requires a row");
        assert_eq!(missing.status, InputStoreStatus::MissingCorrespondence);
        assert!(missing.routes.is_empty());
    });
}

#[test]
fn c03_input_store_preserves_partner_free_outside_the_store_route() {
    let code = OL06.replace(
        "release(&mut cell);",
        "release(&mut cell); free(owner as *mut core::ffi::c_void);",
    );
    with_facts(&code, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let apps = frozen.matched.input_store_applications(facts, store(facts));
        assert_eq!(apps.len(), 1);
        let partner = facts
            .equations
            .iter()
            .find(|e| e.point.function.as_deref() == Some("f") && e.operation == "sink")
            .unwrap();
        let partner = EquationId {
            construction: partner.point.construction,
            ordinal: partner.ordinal,
        };
        assert!(
            apps[0]
                .routes
                .iter()
                .any(|route| route
                    .source_terminals
                    .iter()
                    .any(|meet| meet.terminal.target == TerminalTarget::Free(partner)
                        && route
                            .anchors
                            .iter()
                            .any(|anchor| anchor.source == meet.source))),
            "pre-store copy partner remains a terminal candidate"
        );
    });
}
