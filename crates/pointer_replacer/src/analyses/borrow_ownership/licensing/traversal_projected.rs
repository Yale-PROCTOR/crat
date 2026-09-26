//! F06/C02 projected traversal-call controls; compiler inputs, never executed.
use super::{super::SlotKind, tests::inspect_era5_frame};

pub(crate) const CODE: &str = r#"
unsafe extern "C" { fn malloc(n:usize)->*mut core::ffi::c_void; fn free(p:*mut core::ffi::c_void); }
pub struct Node {left:*mut Node,right:*mut Node,value:i32}
pub struct Holder {ptr:*mut Node, scalar:i32}
pub unsafe fn minimum(mut node:*mut Node)->*mut Node {
    while !(*node).left.is_null(){node=(*node).left;}
    node
}
pub unsafe fn caller()->i32 {
    let root=malloc(core::mem::size_of::<Node>()) as *mut Node;
    (*root).left=0 as *mut Node; (*root).right=0 as *mut Node; (*root).value=7;
    let mut holder=Holder{ptr:root,scalar:0};
    let result=minimum(holder.ptr);
    holder.scalar=9;
    let value=(*result).value;
    free(holder.ptr as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn c08_projected_traversal_keeps_field_owner_and_sibling_write() {
    let fixture = inspect_era5_frame(CODE);
    eprintln!(
        "C08_PROJECTED={}",
        serde_json::json!({
            "accepted":fixture.accepted,"error":fixture.construction_error,
            "kinds":fixture.kinds.iter().map(|(k,v)|(k.clone(),format!("{v:?}"))).collect::<std::collections::BTreeMap<_,_>>(),
            "snapshots":fixture.export.ownership_licensing.as_ref().map(|rows|rows.iter().map(|s|serde_json::json!({
                "offset":s.offset,"field_support":s.field_support,"traversal":s.traversal_correspondences,
                "consumes":s.metadata.consumes,"loads":s.metadata.field_support_inputs.loads,"matched":s.matched,
            })).collect::<Vec<_>>()),
        })
    );
    fixture.assert_kind("Holder.ptr", SlotKind::Owning);
    fixture.assert_kind("caller::result", SlotKind::Ref);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    assert_eq!(accepted.traversal_loans.len(), 1);
    assert!(
        accepted.traversal_loans[0].target.projection.len() > 1,
        "projected owner is not the whole struct"
    );
}

#[test]
fn c08_projected_traversal_payload_write_holds() {
    let code = CODE.replace("holder.scalar=9;", "(*holder.ptr).value=9;");
    let fixture = inspect_era5_frame(&code);
    assert!(fixture.accepted);
    assert!(
        fixture
            .export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .iter()
            .all(|(_, selected)| !*selected)
    );
}

#[test]
fn c08_projected_traversal_deref_field_target_and_metadata() {
    let code = CODE
        .replace(
            "let mut holder=Holder{ptr:root,scalar:0};",
            "let mut storage=Holder{ptr:root,scalar:0};let holder=&mut storage as *mut Holder;",
        )
        .replace("holder.ptr", "(*holder).ptr")
        .replace("holder.scalar", "(*holder).scalar");
    let fixture = inspect_era5_frame(&code);
    eprintln!(
        "C08_DEREF={}",
        serde_json::json!({"commits":fixture.commit_trace,"snapshots":fixture.export.ownership_licensing.as_ref().map(|rows|rows.iter().map(|s|serde_json::json!({"offset":s.offset,"field_support":s.field_support,"traversal":s.traversal_correspondences,"consumes":s.metadata.consumes,"boundaries":s.metadata.boundaries,"matched":s.matched})).collect::<Vec<_>>())})
    );
    fixture.assert_kind("Holder.ptr", SlotKind::Owning);
    fixture.assert_kind("caller::result", SlotKind::Ref);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    let [loan] = accepted.traversal_loans.as_slice() else { panic!("one projected returned loan") };
    assert_eq!(loan.target.projection.len(), 3);
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    assert!(
        super::traversal_call::input_target(&snapshot.metadata.facts(), &loan.origin).is_some(),
        "portable target correspondence must not depend on runtime SlotRef identities"
    );
}

#[test]
fn c08_projected_traversal_discharge_requires_its_exact_guard_and_output() {
    let fixture = inspect_era5_frame(CODE);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    let store = snapshot
        .field_support
        .iter()
        .find(|p| p.field_key == "Holder::field0@d0")
        .unwrap()
        .stores
        .first()
        .unwrap();
    let discharge = store
        .traversal_outputs
        .first()
        .expect("legacy output is conditionally zero");
    let facts = snapshot.metadata.facts();
    assert!(
        super::traversal_discharge::certify(
            &facts,
            &discharge.output,
            &store.meet,
            snapshot.matched.guard_aliases()
        )
        .is_some()
    );
    let mut wrong = store.meet.clone();
    wrong.guards.insert(discharge.proof.candidate.guard, false);
    assert!(
        super::traversal_discharge::certify(
            &facts,
            &discharge.output,
            &wrong,
            snapshot.matched.guard_aliases()
        )
        .is_none(),
        "a false traversal guard cannot discharge its owning output"
    );
    let mut wrong = discharge.output.clone();
    wrong.terminal = store.meet.terminal.clone();
    assert!(
        super::traversal_discharge::certify(
            &facts,
            &wrong,
            &store.meet,
            snapshot.matched.guard_aliases()
        )
        .is_none(),
        "a C free is never discharged"
    );
    let mut wrong = discharge.output.clone();
    if let super::matched::TerminalTarget::Output { node, .. } = &mut wrong.terminal.target {
        node.var += 100000;
    }
    assert!(
        super::traversal_discharge::certify(
            &facts,
            &wrong,
            &store.meet,
            snapshot.matched.guard_aliases()
        )
        .is_none()
    );
}

#[test]
fn c08_projected_traversal_payload_write_with_same_type_sibling_holds() {
    let code = CODE
        .replace(
            "ptr:*mut Node, scalar:i32",
            "ptr:*mut Node, other:*mut Node, scalar:i32",
        )
        .replace(
            "ptr:root,scalar:0",
            "ptr:root,other:0 as *mut Node,scalar:0",
        )
        .replace("holder.scalar=9;", "(*holder.ptr).value=9;");
    let fixture = inspect_era5_frame(&code);
    assert!(fixture.accepted);
    assert!(
        fixture
            .export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .iter()
            .all(|(_, selected)| !*selected),
        "the loan must protect ptr, not its same-type sibling"
    );
}

#[test]
fn s02_traversal_permission_is_mandatory_and_withdraws_for_each_bad_kind() {
    use super::super::{a5_overlap::WholeProgramAttestation, solver::KindSolver};
    super::graph_tests::with_solver_facts(CODE, |facts, original, slots| {
        let mut facts = facts.clone();
        facts.frame_attested = true;
        let _world =
            super::stack_entry::enter_world(Some(WholeProgramAttestation::FrozenBenchmarkGraph));
        let frozen = facts.licensing.as_ref().unwrap();
        let proof = frozen.traversal_correspondences[0].as_ref().unwrap();
        let key = proof.candidate.guard;
        let guard = facts
            .guards
            .iter()
            .find(|g| g.equation == key)
            .unwrap()
            .predicate
            .clone();
        let input = super::traversal_call::input_target(&facts, proof).unwrap();
        let make = || {
            let probe = KindSolver::new(slots);
            let before = probe.hard_assertion_count();
            probe.constrain_traversal_calls(&facts).unwrap();
            assert_eq!(
                probe.hard_assertion_count() - before,
                frozen.traversal_calls.len()
            );
            assert_eq!(
                probe.hard_loop_solver().assertion_count(),
                probe.hard_assertion_count()
            );
            probe
        };
        assert_eq!(
            make().check_with_assumptions(&[guard.clone()]),
            z3::SatResult::Sat
        );
        let denied = [
            (input.kind_key.clone(), SlotKind::Raw),
            (
                format!(
                    "{}::_{}@d0",
                    proof.candidate.call.callee, proof.candidate.parameter
                ),
                SlotKind::Owning,
            ),
            (
                format!("{}::_0@d0", proof.candidate.call.callee),
                SlotKind::Raw,
            ),
            (
                format!(
                    "{}::_{}@d0",
                    proof.candidate.call.caller, proof.native.receiver.local
                ),
                SlotKind::Raw,
            ),
            ("Node::field0@d0".into(), SlotKind::Raw),
        ];
        for (key, kind) in denied {
            let probe = make();
            probe.assume(facts.slot_refs[&key], kind);
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone()]),
                z3::SatResult::Unsat,
                "{key}={kind:?} must hold the traversal permission"
            );
            assert_eq!(
                probe.check_with_assumptions(&[!&guard]),
                z3::SatResult::Sat,
                "held guard restores the ordinary alternative"
            );
        }
        assert_eq!(
            original.check_sat_count(),
            0,
            "construction itself stays zero-query"
        );
    });
}
