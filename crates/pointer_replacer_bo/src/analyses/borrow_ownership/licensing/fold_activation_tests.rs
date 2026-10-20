//! Native synthetic hard/converse controls. Embedded inputs never execute.
use super::{
    super::{
        SlotKind,
        solver::{KindSolver, Selectors},
    },
    facts::Facts,
    fold_chain_tests::CODE,
};

fn with_solver(
    code: &str,
    closed: bool,
    check: impl FnOnce(&KindSolver, &Facts, &Selectors) + Send + Sync,
) {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        use rustc_hir::{ItemKind, OwnerNode};
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::super::crate_slots::CrateSlots::build(&program);
        let origins = super::super::origins::compute_origins(&program);
        let mutability = super::super::mutability_facts::MutFacts::from_program(&program);
        let _world = super::stack_entry::enter_world(
            closed
                .then_some(super::super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        let solver = KindSolver::new(&slots);
        let (construction, _) = super::super::construction::construct_bo_into_a16_refined(
            &program,
            &slots,
            &origins,
            &mutability,
            &solver,
        )
        .unwrap();
        super::super::coherence::constrain_field_ownership(&solver, &slots, &program);
        let facts = solver.ownership_facts().unwrap();
        check(&solver, &facts, &construction.selectors);
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn gf08_activation_native_support_and_original_endpoint_converse() {
    use z3::SatResult::{Sat, Unsat};
    with_solver(CODE, true, |solver, facts, selectors| {
        let proof = facts
            .licensing
            .as_ref()
            .unwrap()
            .fold_callers
            .as_ref()
            .unwrap()[0]
            .outcome
            .as_ref()
            .unwrap();
        let predicate = |key| {
            facts
                .guards
                .iter()
                .find(|g| g.equation == key)
                .unwrap()
                .predicate
                .clone()
        };
        let guard = predicate(proof.guard);
        assert_eq!(selectors.all().len(), 4, "both original source/free pairs");
        assert_eq!(
            solver.check_with_assumptions(&[guard.clone()]),
            Sat,
            "native fold must admit the complete closed caller"
        );
        let mut converse = selectors.all().to_vec();
        converse.push(!&guard);
        assert_eq!(
            solver.check_with_assumptions(&converse),
            Unsat,
            "keeping all original endpoints requires this exact fold"
        );
        for endpoint in [
            proof.payload.source.endpoint,
            proof.payload.free,
            proof.container.source.endpoint,
            proof.container.free,
        ] {
            assert_eq!(
                solver.check_with_assumptions(&[guard.clone(), !predicate(endpoint)]),
                Unsat,
                "selected fold must keep original endpoint {endpoint:?}"
            );
        }
        let own = |node: super::transport::Node| {
            facts.ownership_asts[super::super::ssa::constraint::Var::from_u32(node.var)].clone()
        };
        assert_eq!(
            solver.check_with_assumptions(&[guard.clone(), !own(proof.fold.actual_before)]),
            Unsat
        );
        assert_eq!(
            solver.check_with_assumptions(&[guard.clone(), own(proof.fold.actual_after)]),
            Unsat
        );
        let mut dropped = vec![!&guard];
        dropped.extend(selectors.all().iter().map(|s| !s));
        assert_eq!(
            solver.check_with_assumptions(&dropped),
            Sat,
            "ordinary retracted endpoint model remains available"
        );
        solver.assume(facts.slot_refs[&proof.store.site.field_key], SlotKind::Raw);
        assert_eq!(
            solver.check_with_assumptions(&[guard]),
            Unsat,
            "Raw field cannot select folded ownership"
        );
        let (model, _) = solver
            .model_kinds_relaxing_reporting(selectors)
            .expect("T2 retraction to ordinary model");
        assert_eq!(
            model[&facts.slot_refs[&proof.store.site.field_key]],
            SlotKind::Raw
        );
        let actual = solver.ownership_facts().unwrap();
        assert_eq!(
            solver
                .original_cell_selection()
                .unwrap()
                .value(&actual, proof.guard),
            Some(false)
        );
    });
}

#[test]
fn gf08_activation_open_frame_and_incomplete_callers_remain_held() {
    use z3::SatResult::{Sat, Unsat};
    with_solver(CODE, false, |solver, facts, _| {
        assert!(!facts.frame_attested);
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let guard = &facts
            .guards
            .iter()
            .find(|g| g.equation == declaration.guard)
            .unwrap()
            .predicate;
        assert_eq!(solver.check_with_assumptions(&[guard.clone()]), Unsat);
        assert_eq!(solver.check_with_assumptions(&[!guard]), Sat);
    });
    for code in [
        CODE.replace(" (*holder).ptr=0 as *mut Node;\n", ""),
        CODE.replace(
            " free(result as *mut core::ffi::c_void);",
            " free(node as *mut core::ffi::c_void);\n free(result as *mut core::ffi::c_void);",
        ),
        CODE.replace(
            "pub struct Holder",
            "unsafe extern \"C\"{fn retain(p:*mut Node); }\npub struct Holder",
        )
        .replace(
            " free(result as *mut core::ffi::c_void);",
            " retain(result);\n free(result as *mut core::ffi::c_void);",
        ),
    ] {
        with_solver(&code, true, |solver, facts, _| {
            let row = &facts
                .licensing
                .as_ref()
                .unwrap()
                .fold_callers
                .as_ref()
                .unwrap()[0];
            assert!(row.outcome.is_err());
            let guard = &facts
                .guards
                .iter()
                .find(|g| g.equation == row.declaration.guard)
                .unwrap()
                .predicate;
            assert_eq!(solver.check_with_assumptions(&[guard.clone()]), Unsat);
            assert_eq!(solver.check_with_assumptions(&[!guard]), Sat);
        });
    }
}

/// OC08: the used-child fold is activated by its member certificate, not by the
/// identity one. The identity decision stays held exactly as it was.
#[test]
fn oc08_used_child_fold_activates_through_its_member_certificate() {
    use z3::SatResult::{Sat, Unsat};
    with_solver(
        super::fold_subtree_tests::CODE,
        true,
        |solver, facts, selectors| {
            let licensing = facts.licensing.as_ref().unwrap();
            assert!(
                licensing.fold_callers.as_ref().unwrap()[0].outcome.is_err(),
                "the identity certificate still cannot admit a used descendant"
            );
            let proof = licensing.fold_members.as_ref().unwrap()[0]
                .outcome
                .as_ref()
                .expect("the used-child member certificate");
            let predicate = |key| {
                facts
                    .guards
                    .iter()
                    .find(|g| g.equation == key)
                    .unwrap()
                    .predicate
                    .clone()
            };
            let guard = predicate(proof.guard);
            assert_eq!(
                solver.check_with_assumptions(&[guard.clone()]),
                Sat,
                "the member fold must be admissible, not forced pending"
            );
            let mut converse = selectors.all().to_vec();
            converse.push(!&guard);
            assert_eq!(
                solver.check_with_assumptions(&converse),
                Unsat,
                "keeping every original endpoint requires this exact fold"
            );
            for endpoint in &proof.endpoints {
                assert_eq!(
                    solver.check_with_assumptions(&[guard.clone(), !predicate(*endpoint)]),
                    Unsat,
                    "the selected member fold must keep original endpoint {endpoint:?}"
                );
            }
            let own = |node: super::transport::Node| {
                facts.ownership_asts[super::super::ssa::constraint::Var::from_u32(node.var)].clone()
            };
            assert_eq!(
                solver
                    .check_with_assumptions(&[guard.clone(), !own(proof.membership.member_before)]),
                Unsat,
                "the member's pre-narrow component owns under the fold"
            );
            assert_eq!(
                solver.check_with_assumptions(&[guard.clone(), own(proof.membership.member_after)]),
                Unsat,
                "and its after-component is zero"
            );
        },
    );
}

/// A callee whose body is not straight-line: the fold declaration still exists,
/// but no certificate can qualify, so nothing may activate.
const BRANCHING_DETACH: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let child=(*node).child;
 if child.is_null() { return 0 as *mut Node; }
 free(node as *mut core::ffi::c_void);
 child
}
pub unsafe fn run(){
 let leaf=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*leaf).child=0 as *mut Node;
 let parent=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*parent).child=leaf;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=parent;
 let result=detach((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;

/// R310-1(owed): the member arm activates only inside a closed frame. The open
/// frame is the witnessed half; the unsupported-callee half is a shape control
/// whose refusal is produced upstream, where no certificate qualifies at all.
#[test]
fn oc11_the_member_arm_stays_pending_outside_a_closed_frame() {
    use z3::SatResult::Unsat;
    with_solver(
        super::fold_subtree_tests::CODE,
        false,
        |solver, facts, _| {
            let licensing = facts.licensing.as_ref().unwrap();
            let proof = licensing.fold_members.as_ref().unwrap()[0]
                .outcome
                .as_ref()
                .expect("the member certificate itself does not depend on the frame");
            let guard = facts
                .guards
                .iter()
                .find(|g| g.equation == proof.guard)
                .unwrap()
                .predicate
                .clone();
            assert_eq!(
                solver.check_with_assumptions(&[guard]),
                Unsat,
                "an open frame leaves the member fold pending"
            );
        },
    );
}

#[test]
fn oc11_an_unsupported_callee_shape_activates_nothing() {
    use z3::SatResult::Unsat;
    with_solver(BRANCHING_DETACH, true, |solver, facts, _| {
        let licensing = facts.licensing.as_ref().unwrap();
        let [identity] = licensing.fold_callers.as_deref().unwrap() else {
            panic!("one declaration")
        };
        assert!(identity.outcome.is_err(), "{:?}", identity.outcome);
        assert_eq!(
            licensing.fold_members.as_deref().unwrap(),
            &[],
            "a refusal that is not about a used descendant yields no member decision"
        );
        let guard = facts
            .guards
            .iter()
            .find(|g| g.equation == identity.declaration.guard)
            .unwrap()
            .predicate
            .clone();
        assert_eq!(
            solver.check_with_assumptions(&[guard]),
            Unsat,
            "nothing certified, nothing activated"
        );
    });
}

/// The closed-frame contrast can differ: the base frame is satisfiable either
/// way, so the open-frame refusal is the fold guard's, not a dead solver.
#[test]
fn oc11_the_closed_frame_contrast_is_not_vacuous() {
    use z3::SatResult::{Sat, Unsat};
    for closed in [true, false] {
        with_solver(
            super::fold_subtree_tests::CODE,
            closed,
            move |solver, facts, _| {
                assert_eq!(facts.frame_attested, closed);
                assert_eq!(
                    solver.check_with_assumptions(&[]),
                    Sat,
                    "the base frame is satisfiable either way"
                );
                let proof = facts
                    .licensing
                    .as_ref()
                    .unwrap()
                    .fold_members
                    .as_ref()
                    .unwrap()[0]
                    .outcome
                    .as_ref()
                    .expect("the certificate does not depend on the frame");
                let guard = facts
                    .guards
                    .iter()
                    .find(|g| g.equation == proof.guard)
                    .unwrap()
                    .predicate
                    .clone();
                assert_eq!(
                    solver.check_with_assumptions(&[guard]),
                    if closed { Sat } else { Unsat },
                    "the frame is what moves the guard"
                );
            },
        );
    }
}
