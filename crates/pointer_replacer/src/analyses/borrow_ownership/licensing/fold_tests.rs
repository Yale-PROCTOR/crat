//! R288 folded-subtree controls. Embedded code is compiler input, never executed.
use super::graph_tests::with_facts;

const TYPES: &str = r#"
pub struct Node { pub value:i32, pub child:*mut Node }
pub struct Other { pub child:*mut Other }
pub unsafe fn identity(node:*mut Node)->*mut Node {node}
pub unsafe fn caller(node:*mut Node)->*mut Node {identity((*node).child)}
pub unsafe fn other(node:*mut Other)->*mut Other {node}
"#;

#[test]
fn gf02_compiler_types_name_actual_formal_and_distinct_structures() {
    with_facts(TYPES, |facts| {
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let value = serde_json::to_value(&snapshot).unwrap();
        let types = &value["metadata"]["fold_types"];
        assert!(
            types.is_object(),
            "G-FOLD requires compiler type evidence independent of Var offsets"
        );
        let places = types["places"].as_array().unwrap();
        assert!(
            places.iter().any(|p| p["function"] == "caller"
                && p["place"]["projection"]
                    .as_array()
                    .is_some_and(|p| !p.is_empty())),
            "actual projected field has a compiler type"
        );
        let structures = types["structures"].as_array().unwrap();
        assert!(structures.iter().any(|s| s["identity"] == "Node"));
        assert!(structures.iter().any(|s| s["identity"] == "Other"));
        snapshot.validate().unwrap();
    });
}

#[test]
fn gf02_type_evidence_survives_ast_free_metadata_reconstruction() {
    with_facts(TYPES, |facts| {
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let before = serde_json::to_value(&snapshot.metadata).unwrap();
        assert!(
            before["fold_types"].is_object(),
            "fold type availability is explicit"
        );
        let rebuilt =
            super::snapshot::Metadata::from_facts(&snapshot.metadata.facts(), &snapshot.matched);
        assert_eq!(
            serde_json::to_value(rebuilt).unwrap()["fold_types"],
            before["fold_types"]
        );
    });
}

#[test]
fn gf02_type_arguments_and_union_targets_are_not_conflated() {
    with_facts(
        r#"
pub struct N<T>{child:*mut N<T>,value:T}
pub union U{pointer:*mut i32,integer:usize}
pub unsafe fn first(p:*mut N<i32>)->*mut N<i32>{p}
pub unsafe fn second(p:*mut N<u64>)->*mut N<u64>{p}
pub unsafe fn union_target(p:*mut U)->*mut U{p}
"#,
        |facts| {
            let types = facts.fold_types.as_ref().unwrap();
            let root = |name| {
                types
                    .places
                    .iter()
                    .find(|p| {
                        p.function == name && p.place.local == 1 && p.place.projection.is_empty()
                    })
                    .unwrap()
            };
            assert_eq!(root("first").pointee_struct, root("second").pointee_struct);
            assert_ne!(root("first").pointee_type, root("second").pointee_type);
            assert!(root("union_target").pointee_struct.is_none());
            assert!(!types.structures.iter().any(|s| s.identity == "U"));
            let unique: std::collections::BTreeSet<_> = types.places.iter().collect();
            assert_eq!(unique.len(), types.places.len());
        },
    );
}

const TAKE: &str = r#"
unsafe extern "C" { fn free(p:*mut core::ffi::c_void); }
pub struct Node { child:*mut Node }
pub unsafe fn detach(node:*mut Node)->*mut Node {
    let child=(*node).child;
    free(node as *mut core::ffi::c_void);
    child
}
"#;

#[test]
fn gf03_terminal_coverage_enumerates_every_local_and_preserves_zero_laws() {
    with_facts(TAKE, |facts| {
        let inventory = super::fold_coverage::validate(facts, 0, "detach").unwrap();
        let expected: Vec<_> = facts
            .terminals
            .iter()
            .filter(|t| t.point.function.as_deref() == Some("detach"))
            .map(|t| t.ordinal)
            .collect();
        assert_eq!(
            inventory, expected,
            "full terminal inventory, not only present-row consistency"
        );
    });
}

#[test]
fn gf03_joint_terminal_and_zero_omission_is_typed() {
    use super::super::ownership_occurrence::Availability;
    with_facts(TAKE, |facts| {
        let terminal = facts
            .terminals
            .iter()
            .find(|t| {
                t.role == "local-final-zero"
                    && matches!(&t.values,Availability::Present(v) if !v.is_empty())
            })
            .unwrap()
            .clone();
        let Availability::Present(values) = &terminal.values else { unreachable!() };
        let mut bad = facts.clone();
        bad.terminals.retain(|t| t.ordinal != terminal.ordinal);
        bad.equations.retain(|e| {
            !(e.point == terminal.point
                && e.assumption_class.as_deref() == Some("temporary-finalization")
                && e.variables
                    .iter()
                    .any(|v| values.iter().any(|x| x.var == *v)))
        });
        assert_eq!(
            super::fold_coverage::validate(&bad, 0, "detach"),
            Err(super::fold_coverage::Error::MissingTerminal {
                block: terminal.point.block.unwrap(),
                statement: terminal.point.statement.unwrap(),
                local: terminal.local
            })
        );
    });
}

#[test]
fn gf03_selection_cannot_omit_a_nonreturn_local() {
    with_facts(TAKE, |facts| {
        let mut bad = facts.clone();
        let row = &mut bad.return_selections[0];
        let point = row.point.clone();
        let local = row.locals.iter().find(|(local, _)| *local > 0).unwrap().0;
        row.locals.retain(|(l, _)| *l != local);
        assert_eq!(
            super::fold_coverage::validate(&bad, 0, "detach"),
            Err(super::fold_coverage::Error::LocalCoverage {
                block: point.block.unwrap(),
                statement: point.statement.unwrap()
            })
        );
    });
}

#[test]
fn gf03_joint_selection_terminal_zero_omission_keeps_compiler_local_denominator() {
    use super::super::ownership_occurrence::Availability;
    with_facts(TAKE, |facts| {
        let terminal = facts
            .terminals
            .iter()
            .find(|t| {
                t.role == "local-final-zero"
                    && matches!(&t.values,Availability::Present(v) if !v.is_empty())
            })
            .unwrap()
            .clone();
        let Availability::Present(values) = &terminal.values else { unreachable!() };
        let mut bad = facts.clone();
        bad.terminals.retain(|t| t.ordinal != terminal.ordinal);
        bad.return_selections
            .iter_mut()
            .filter(|r| r.point == terminal.point)
            .for_each(|r| r.locals.retain(|(local, _)| *local != terminal.local));
        bad.equations.retain(|e| {
            !(e.point == terminal.point
                && e.assumption_class.as_deref() == Some("temporary-finalization")
                && e.variables
                    .iter()
                    .any(|v| values.iter().any(|x| x.var == *v)))
        });
        assert_eq!(
            super::fold_coverage::validate(&bad, 0, "detach"),
            Err(super::fold_coverage::Error::LocalCoverage {
                block: terminal.point.block.unwrap(),
                statement: terminal.point.statement.unwrap()
            }),
            "compiler locals cannot disappear with their selected terminal and zero"
        );
    });
}

#[test]
fn gf04_identity_return_has_a_conditional_full_width_internal_certificate() {
    with_facts(TYPES, |facts| {
        let proof = super::fold_internal::certify_linear(facts, 0, "identity", 1)
            .expect("owned identity returns its subtree");
        assert_eq!(proof.structure, "Node");
        assert!(
            proof.used_fields.is_empty(),
            "unchanged descendant is eligible for the unused arm"
        );
        assert!(!proof.terminal_inventory.is_empty());
    });
}

#[test]
fn gf04_take_child_before_parent_free_returns_one_subtree() {
    with_facts(TAKE, |facts| {
        let proof = super::fold_internal::certify_linear(facts, 0, "detach", 1)
            .expect("taken child survives the original parent free");
        assert_eq!(proof.used_fields, vec!["Node::field0@d0"]);
        assert!(
            proof
                .actions
                .iter()
                .any(|a| a.kind == "take" && !a.zero_requirements.is_empty()),
            "old parent field cleared by the selected take, not by sink def zeros"
        );
        assert!(proof.actions.iter().any(|a| a.kind == "free"));
    });
}

#[test]
fn gf04_parent_free_without_taking_child_is_internal_rejection() {
    with_facts(
        r#"
unsafe extern "C" {fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub unsafe fn leak(node:*mut Node){free(node as *mut core::ffi::c_void);}
"#,
        |facts| {
            assert_eq!(
                super::fold_internal::certify_linear(facts, 0, "leak", 1),
                Err(super::fold_internal::Error::ParentFreeWithLiveDescendant)
            )
        },
    );
}

#[test]
fn gf04_global_and_returned_descendant_is_internal_rejection() {
    with_facts(
        r#"
unsafe extern "C" {fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
static mut SAVED:*mut Node=0 as *mut Node;
pub unsafe fn duplicate(node:*mut Node)->*mut Node{
 let child=(*node).child;free(node as *mut core::ffi::c_void);SAVED=child;child
}

"#,
        |facts| {
            assert_eq!(
                super::fold_internal::certify_linear(facts, 0, "duplicate", 1),
                // Retyped by R317-2. This fixture stores into a `static mut`,
                // so it is the escape half of the gate, not the deferred
                // G-FIELD half; both share it until (a) splits them.
                Err(super::fold_internal::Error::PointerDestinationStore)
            )
        },
    );
}

#[test]
fn gf04_retained_field_read_stays_held_in_initial_internal_subset() {
    with_facts(
        r#"
pub struct Node{child:*mut Node}
pub unsafe fn inspect(node:*mut Node)->*mut Node{let observed=(*node).child;node}
"#,
        |facts| {
            assert!(
                matches!(
                    super::fold_internal::certify_linear(facts, 0, "inspect", 1),
                    // Retyped: a retained read sends the value two places, which
                    // is an ambiguous route, not a return that leaves a
                    // component unaccounted for.
                    Err(super::fold_internal::Error::AmbiguousRoute { choices: 2, .. })
                ),
                "unsupported retained-read shape has no certificate and cannot claim unused-field folding"
            );
        },
    );
}

#[test]
fn gf04_joint_internal_boundary_pair_and_equation_omission_is_rejected() {
    use super::super::ownership_boundary::{Role, Variables};
    with_facts(TYPES, |facts| {
        for role in [Role::Entry, Role::ExitReturn, Role::ExitOutput] {
            let mut bad = facts.clone();
            let boundary = bad
                .boundary_substitutions
                .iter_mut()
                .find(|b| b.point.function.as_deref() == Some("identity") && b.role == role)
                .unwrap();
            let pair = boundary.matched.pop().unwrap();
            let point = boundary.point.clone();
            let (Variables::Single { var: actual }, Variables::Single { var: formal }) =
                (pair.actual, pair.formal)
            else {
                panic!("internal single window")
            };
            bad.equations.retain(|e| {
                !(e.point == point && e.operation == "equal" && e.variables == [actual, formal])
            });
            assert_eq!(
                super::fold_internal::certify_linear(&bad, 0, "identity", 1),
                Err(super::fold_internal::Error::BoundaryCoverage),
                "{role:?} pair and its equation may not disappear together"
            );
        }
    });
}

#[test]
fn gf04_projection_frames_are_required_before_parent_free() {
    use super::super::{export::ProjKey, ownership_occurrence::Availability::Present};
    with_facts(
        r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node,value:i32}
pub unsafe fn detach(node:*mut Node)->*mut Node{
 let child=(*node).child;(*node).value=0;free(node as *mut core::ffi::c_void);child
}
"#,
        |facts| {
            super::fold_internal::certify_linear(facts, 0, "detach", 1)
                .expect("complete child-zero path before free");
            let consume = facts
                .consumes
                .iter()
                .find(|c| c.local == 1 && c.projection == [ProjKey::Deref, ProjKey::Field(0)])
                .unwrap();
            let (Present(base), Present(paths)) = (&consume.base, &consume.pointer_paths) else {
                panic!("full base paths")
            };
            let offset = paths.iter().position(Vec::is_empty).unwrap() as u32;
            let mut bad = facts.clone();
            let before = bad.equations.len();
            bad.equations.retain(|e| {
                !(e.point == consume.point
                    && e.operation == "equal"
                    && e.transfer.is_none()
                    && e.variables == [base.use_start + offset, base.def_start + offset])
            });
            assert_eq!(
                bad.equations.len() + 1,
                before,
                "remove only the parent frame at the actual child take"
            );
            assert_eq!(
                super::fold_internal::certify_linear(&bad, 0, "detach", 1),
                Err(super::fold_internal::Error::FrameCoverage),
                "the full internal certificate requires the exact projection frame"
            );
        },
    );
}

#[test]
fn gf04_post_take_parent_copy_requires_descendant_zero_transfer() {
    with_facts(
        r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node,value:i32}
pub unsafe fn detach(node:*mut Node)->*mut Node{
 let child=(*node).child;let parent=node;(*parent).value=0;
 free(parent as *mut core::ffi::c_void);child
}
"#,
        |facts| {
            use super::super::ownership_occurrence::{Availability::Present, PathStep};
            super::fold_internal::certify_linear(facts, 0, "detach", 1)
                .expect("intact post-take parent copy");
            let equation=facts.equations.iter().find(|e|e.point.function.as_deref()==Some("detach")
            && matches!(e.operation.as_str(),"linear"|"equal"|"guarded-copy"|"guarded-move")
            && e.transfer.as_ref().is_some_and(|t|matches!((&t.source,&t.destination),(Present(source),Present(destination))
                if source.local==1 && source.projection.is_empty() && destination.projection.is_empty()
                    && matches!(source.path.last(),Some(PathStep::Field{index:0,..}))))).expect("actual descendant transfer on full-width parent copy");
            let transfer = equation.transfer.as_ref().unwrap();
            assert!(
                facts.equations.iter().any(|e| e.point == equation.point
                    && e.operation == "assume"
                    && e.value == Some(false)
                    && e.variables == [transfer.destination_use]),
                "old-zero retained"
            );
            let mut bad = facts.clone();
            bad.equations.retain(|e| {
                e.point.construction != equation.point.construction || e.ordinal != equation.ordinal
            });
            assert_eq!(
                super::fold_internal::certify_linear(&bad, 0, "detach", 1),
                Err(super::fold_internal::Error::MissingTransferGap(
                    super::fold_internal::TransferGap::ComponentLawAbsent
                )),
                "zero descendant responsibility must cross the parent copy before its free"
            );
            bad.equations.retain(|e| {
                !(e.point == equation.point
                    && e.operation == "assume"
                    && e.value == Some(false)
                    && e.variables == [transfer.destination_use])
            });
            assert_eq!(
                super::fold_internal::certify_linear(&bad, 0, "detach", 1),
                // Measured: the law is already gone, so dropping its old-zero
                // as well lands on the same refusal — which is the point the
                // message makes, now said by the gap itself.
                Err(super::fold_internal::Error::MissingTransferGap(
                    super::fold_internal::TransferGap::ComponentLawAbsent
                )),
                "joint law/old-zero omission cannot shrink the source-component denominator"
            );
        },
    );
}

#[test]
fn gf04_internal_certificate_rebuilds_without_guard_asts() {
    with_facts(TAKE, |facts| {
        let live = super::fold_internal::certify_linear(facts, 0, "detach", 1).unwrap();
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let rebuilt = snapshot.metadata.facts();
        assert!(rebuilt.guards.is_empty());
        assert_eq!(
            super::fold_internal::certify_linear_metadata(
                &rebuilt,
                0,
                "detach",
                1,
                &snapshot.metadata.guard_aliases.iter().copied().collect()
            ),
            Ok(live)
        );
    });
}

#[test]
fn gf04_internal_metadata_requires_the_original_free_alias() {
    with_facts(TAKE, |facts| {
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let rebuilt = snapshot.metadata.facts();
        let mut aliases: std::collections::BTreeMap<_, _> =
            snapshot.metadata.guard_aliases.iter().copied().collect();
        let sink = rebuilt
            .equations
            .iter()
            .find(|e| e.operation == "sink" && e.point.function.as_deref() == Some("detach"))
            .unwrap();
        assert!(
            aliases
                .remove(&super::facts::EquationId {
                    construction: 0,
                    ordinal: sink.ordinal
                })
                .is_some()
        );
        assert!(
            matches!(
                super::fold_internal::certify_linear_metadata(&rebuilt, 0, "detach", 1, &aliases),
                Err(super::fold_internal::Error::Coverage(_))
            ),
            "the family is the identity asserted; R332-2 attributes the line"
        );
    });
}

#[test]
fn gf04_pre_free_child_zero_has_an_explicit_derivation() {
    with_facts(TAKE, |facts| {
        let proof = super::fold_internal::certify_linear(facts, 0, "detach", 1).unwrap();
        let take = proof.actions.iter().find(|a| a.kind == "take").unwrap();
        let zero = proof
            .actions
            .iter()
            .find(|a| a.kind == "pre-free-child-zero")
            .expect("parent descendant use has a pre-free zero derivation, never a sink-def zero");
        assert!(!zero.zero_requirements.is_empty());
        assert!(zero.equations.iter().all(|id| facts.equations.iter().any(
            |e| e.point.construction == id.construction
                && e.ordinal == id.ordinal
                && e.operation != "sink"
                && e.assumption_class.as_deref() != Some("temporary-finalization")
        )));
        assert!(
            take.equations.iter().all(|id| zero.equations.contains(id)),
            "pre-free zero derives from the take across the actual SSA transitions"
        );
        assert!(zero.zero_requirements.iter().all(|node|facts.consumes.iter().any(|consume|
            consume.point.function.as_deref()==Some("detach")
            && consume.point.block==Some(zero.block) && consume.point.statement==Some(zero.statement)
            && matches!(&consume.projected,super::super::ownership_occurrence::Availability::Present(window)
                if node.var>window.use_start && node.var<window.use_end))),
            "target is an actual pre-free descendant use component");
    });
}

fn fold_call_key(facts: &super::facts::Facts, callee: &str) -> super::matched::CallKey {
    let boundary = facts
        .boundary_substitutions
        .iter()
        .find(|b| {
            b.role == super::super::ownership_boundary::Role::CallArgument
                && b.callee.as_deref() == Some(callee)
        })
        .unwrap();
    super::matched::CallKey {
        construction: boundary.point.construction,
        caller: boundary.point.function.clone().unwrap(),
        block: boundary.point.block.unwrap(),
        statement: boundary.point.statement.unwrap(),
        callee: callee.into(),
    }
}

#[test]
fn gf05_identity_child_call_covers_exact_formal_tails_without_adding_components() {
    with_facts(TYPES, |facts| {
        let call = fold_call_key(facts, "identity");
        let proof = super::fold_call::certify(facts, &call, 0, &Default::default())
            .expect("conditional fold of the exact child cell");
        let boundary = facts
            .boundary_substitutions
            .iter()
            .find(|b| b.ordinal == proof.boundary)
            .unwrap();
        let mut expected = boundary.unmatched_formal_vars.clone();
        expected.sort_unstable();
        let mut actual: Vec<_> = proof
            .descendants
            .iter()
            .flat_map(|d| [d.formal_use, d.formal_def])
            .collect();
        actual.sort_unstable();
        assert!(!expected.is_empty());
        assert_eq!(actual, expected);
        assert!(boundary.unmatched_actual_vars.is_empty());
        assert!(proof.requires_consuming_root);
        assert!(
            proof
                .descendants
                .iter()
                .all(|d| matches!(d.premise, super::fold_call::FieldPremise::Unused { .. }))
        );
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        assert_eq!(
            super::fold_call::certify_metadata(
                &snapshot.metadata.facts(),
                &call,
                0,
                &Default::default(),
                &snapshot.metadata.guard_aliases.iter().copied().collect()
            ),
            Ok(proof)
        );
    });
}

#[test]
fn gf05_accessed_descendant_requires_the_owning_field_scheme() {
    let code = format!(
        "{}\npub unsafe fn caller(node:*mut Node)->*mut Node{{detach((*node).child)}}",
        TAKE
    );
    with_facts(&code, |facts| {
        let call = fold_call_key(facts, "detach");
        let field = facts
            .fold_types
            .as_ref()
            .unwrap()
            .structures
            .iter()
            .find(|s| s.identity == "Node")
            .unwrap()
            .fields[0]
            .field_key
            .clone()
            .unwrap();
        assert_eq!(
            super::fold_call::certify(facts, &call, 0, &Default::default()),
            Err(super::fold_call::Error::FieldScheme(field.clone()))
        );
        let proof =
            super::fold_call::certify(facts, &call, 0, &[field.clone()].into_iter().collect())
                .expect("conditional owning-field fold");
        assert!(proof.descendants.iter().all(|d| d.premise
            == super::fold_call::FieldPremise::Owning {
                field: field.clone()
            }));
    });
}

#[test]
fn gf05_parent_with_stored_child_requires_its_internal_certificate() {
    with_facts(
        r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub unsafe fn leak(node:*mut Node){free(node as *mut core::ffi::c_void);}
pub unsafe fn caller(node:*mut Node){leak((*node).child);}
"#,
        |facts| {
            let call = fold_call_key(facts, "leak");
            let field = facts
                .fold_types
                .as_ref()
                .unwrap()
                .structures
                .iter()
                .find(|s| s.identity == "Node")
                .unwrap()
                .fields[0]
                .field_key
                .clone()
                .unwrap();
            assert_eq!(
                super::fold_call::certify(facts, &call, 0, &[field].into_iter().collect()),
                Err(super::fold_call::Error::Internal(
                    super::fold_internal::Error::ParentFreeWithLiveDescendant
                ))
            );
        },
    );
}

#[test]
fn gf05_fold_keeps_exact_type_and_complete_argument_tail_denominators() {
    with_facts(TYPES, |facts| {
        let call = fold_call_key(facts, "identity");
        let proof = super::fold_call::certify(facts, &call, 0, &Default::default()).unwrap();
        let mut bad = facts.clone();
        bad.boundary_substitutions
            .iter_mut()
            .find(|b| b.ordinal == proof.boundary)
            .unwrap()
            .unmatched_formal_vars
            .pop()
            .unwrap();
        assert_eq!(
            super::fold_call::certify(&bad, &call, 0, &Default::default()),
            Err(super::fold_call::Error::Boundary)
        );
        let mut bad = facts.clone();
        let consume = facts
            .consumes
            .iter()
            .find(|c| c.ordinal == proof.actual_consume)
            .unwrap();
        let actual = bad
            .fold_types
            .as_mut()
            .unwrap()
            .places
            .iter_mut()
            .find(|p| {
                p.function == call.caller
                    && p.place.local == consume.local
                    && p.place.projection == consume.projection
            })
            .unwrap();
        actual.pointee_struct = Some("Other".into());
        assert_eq!(
            super::fold_call::certify(&bad, &call, 0, &Default::default()),
            Err(super::fold_call::Error::Type)
        );
    });
}

#[test]
fn gf05_joint_receiver_match_and_equation_omission_is_rejected() {
    use super::super::ownership_boundary::Variables;
    with_facts(TYPES, |facts| {
        let call = fold_call_key(facts, "identity");
        let proof = super::fold_call::certify(facts, &call, 0, &Default::default()).unwrap();
        let mut bad = facts.clone();
        let receiver = bad
            .boundary_substitutions
            .iter_mut()
            .find(|b| b.ordinal == proof.receiver_boundary)
            .unwrap();
        assert!(receiver.matched.len() > 1, "actual full-width receiver");
        let pair = receiver.matched.pop().unwrap();
        let point = receiver.point.clone();
        let (Variables::UseDef { def_var, .. }, Variables::Single { var }) =
            (pair.actual, pair.formal)
        else {
            panic!("native return pair")
        };
        let before = bad.equations.len();
        bad.equations.retain(|e| {
            !(e.point == point && e.operation == "equal" && e.variables == [def_var, var])
        });
        assert_eq!(
            bad.equations.len() + 1,
            before,
            "remove only the omitted tail's native equation"
        );
        assert_eq!(
            super::fold_call::certify(&bad, &call, 0, &Default::default()),
            Err(super::fold_call::Error::Boundary)
        );
    });
}

#[test]
fn gf05_call_requires_native_source_and_compiler_call_membership() {
    with_facts(TYPES, |facts| {
        let call = fold_call_key(facts, "identity");
        for remove_source in [true, false] {
            let mut bad = facts.clone();
            if remove_source {
                bad.source_occurrences
                    .get_mut(&call.caller)
                    .unwrap()
                    .retain(|o| o.site.block != call.block || o.site.statement != call.statement);
            } else {
                let coverage = bad.caller_coverage.as_mut().unwrap();
                let before = coverage.local_calls.len();
                coverage.local_calls.retain(|c| {
                    c.site.function != call.caller
                        || c.site.block != call.block
                        || c.site.statement != call.statement
                        || c.target != call.callee
                });
                assert_eq!(coverage.local_calls.len() + 1, before);
            }
            assert_eq!(
                super::fold_call::certify(&bad, &call, 0, &Default::default()),
                Err(super::fold_call::Error::NativeCall),
                "native source removal={remove_source}"
            );
        }
    });
}

#[test]
fn gf05_argument_proxy_must_be_the_native_call_operand() {
    with_facts(TYPES, |facts| {
        let call = fold_call_key(facts, "identity");
        let proof = super::fold_call::certify(facts, &call, 0, &Default::default()).unwrap();
        let boundary = facts
            .boundary_substitutions
            .iter()
            .find(|b| b.ordinal == proof.boundary)
            .unwrap();
        let super::super::ownership_occurrence::Availability::Present(id) =
            boundary.call_arg_registration
        else {
            panic!("native proxy")
        };
        let mut bad = facts.clone();
        let registration = bad
            .call_arg_registrations
            .iter_mut()
            .find(|r| r.ordinal == id)
            .unwrap();
        registration.proxy_local += 1000;
        assert_eq!(
            super::fold_call::certify(&bad, &call, 0, &Default::default()),
            Err(super::fold_call::Error::NativeCall)
        );
    });
}

#[test]
fn gf05_internal_admission_killer_has_a_fully_joined_pointer_return() {
    with_facts(
        r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub unsafe fn leak(node:*mut Node)->*mut Node{free(node as *mut core::ffi::c_void);0 as *mut Node}
pub unsafe fn caller(node:*mut Node)->*mut Node{leak((*node).child)}
"#,
        |facts| {
            let call = fold_call_key(facts, "leak");
            let field = facts
                .fold_types
                .as_ref()
                .unwrap()
                .structures
                .iter()
                .find(|s| s.identity == "Node")
                .unwrap()
                .fields[0]
                .field_key
                .clone()
                .unwrap();
            let candidate=super::fold_call::join_native(facts,&call,0,&[field.clone()].into_iter().collect(),&[field])
            .expect("all pointer call/entry/output/receiver/type joins survive without internal admission");
            assert!(!candidate.descendants.is_empty());
            let internal = super::fold_internal::certify_linear(facts, 0, "leak", 1);
            assert_eq!(
                internal,
                Err(super::fold_internal::Error::ParentFreeWithLiveDescendant)
            );
            assert_eq!(
                super::fold_call::admit_internal(&internal),
                Err(super::fold_call::Error::Internal(
                    super::fold_internal::Error::ParentFreeWithLiveDescendant
                )),
                "G-FOLD(c) production admission must reject the joined leaking callee"
            );
        },
    );
}

#[test]
fn gf06_permission_binds_selected_kinds_rho_and_original_endpoint() {
    use z3::{SatResult, ast::Bool};

    use super::super::{domain::SlotKind, solver::KindSolver, ssa::constraint::Var};
    let code = format!(
        "{}\npub struct Holder{{ptr:*mut Node}}\npub unsafe fn caller(holder:*mut Holder)->*mut Node{{detach((*holder).ptr)}}",
        TAKE
    );
    super::graph_tests::with_solver_facts(&code, |facts, original, slots| {
        let mut observed = facts.clone();
        observed.frame_attested = true;
        let facts = &observed;
        let _world = super::stack_entry::enter_world(Some(
            super::super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ));
        let call = fold_call_key(facts, "detach");
        let proof = super::fold_call::certify(
            facts,
            &call,
            0,
            &["Node::field0@d0".into()].into_iter().collect(),
        )
        .unwrap();
        let guard = Bool::fresh_const("gf06-forced-fold");
        let make = || {
            let probe = KindSolver::new(slots);
            probe
                .constrain_fold_permission(facts, &proof, &guard)
                .unwrap();
            probe
        };
        assert_eq!(
            make().check_with_assumptions(&[guard.clone()]),
            SatResult::Sat,
            "conditional gate has a consistent owning arm"
        );
        let receiver = facts
            .boundary_substitutions
            .iter()
            .find(|b| b.ordinal == proof.receiver_boundary)
            .unwrap();
        let super::super::ownership_occurrence::Availability::Present(id) =
            receiver.actual_occurrence
        else {
            panic!("receiver")
        };
        let local = facts
            .consumes
            .iter()
            .find(|c| c.ordinal == id)
            .unwrap()
            .local;
        for (key, kind) in [
            ("Holder::field0@d0".into(), SlotKind::Raw),
            ("Holder::field0@d0".into(), SlotKind::Ref),
            ("Node::field0@d0".into(), SlotKind::Raw),
            ("detach::_1@d0".into(), SlotKind::Ref),
            ("detach::_0@d0".into(), SlotKind::Raw),
            (format!("caller::_{local}@d0"), SlotKind::Raw),
        ] {
            let probe = make();
            probe.assume(facts.slot_refs[&key], kind);
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone()]),
                SatResult::Unsat,
                "{key}={kind:?} must hold the fold"
            );
            assert_eq!(
                probe.check_with_assumptions(&[!&guard]),
                SatResult::Sat,
                "withdrawing fold restores alternatives"
            );
        }
        let rho =
            |node: super::transport::Node| facts.ownership_asts[Var::from_u32(node.var)].clone();
        let mut bad = vec![
            !rho(proof.actual_before),
            rho(proof.actual_after),
            !rho(proof.receiver),
        ];
        bad.extend(
            proof
                .internal
                .actions
                .iter()
                .flat_map(|a| a.zero_requirements.iter())
                .map(|n| rho(*n)),
        );
        bad.extend(
            proof
                .internal
                .required_guards
                .iter()
                .map(|(key, positive)| {
                    let g = facts
                        .guards
                        .iter()
                        .find(|g| g.equation == *key)
                        .unwrap()
                        .predicate
                        .clone();
                    if *positive { !g } else { g }
                }),
        );
        for rejected in bad {
            let probe = make();
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone(), rejected.clone()]),
                SatResult::Unsat
            );
            assert_eq!(
                probe.check_with_assumptions(&[!&guard, rejected]),
                SatResult::Sat
            );
        }
        let probe = KindSolver::new(slots);
        let before = probe.hard_assertion_count();
        probe
            .constrain_fold_permission(facts, &proof, &guard)
            .unwrap();
        assert_eq!(
            probe.hard_assertion_count(),
            before + 1,
            "mandatory fold implication"
        );
        assert_eq!(
            probe.hard_loop_solver().assertion_count(),
            probe.hard_assertion_count()
        );
        let mut unframed = facts.clone();
        unframed.frame_attested = false;
        let probe = KindSolver::new(slots);
        probe
            .constrain_fold_permission(&unframed, &proof, &guard)
            .unwrap();
        assert_eq!(
            probe.check_with_assumptions(&[guard.clone()]),
            SatResult::Unsat
        );
        assert_eq!(probe.check_with_assumptions(&[!&guard]), SatResult::Sat);
        assert_eq!(
            original.check_sat_count(),
            0,
            "original construction stays zero-query"
        );
    });
}

#[test]
fn gf06_requirements_rebuild_without_asts_or_native_slot_ids() {
    let code = format!(
        "{}\npub struct Holder{{ptr:*mut Node}}\npub unsafe fn caller(holder:*mut Holder)->*mut Node{{detach((*holder).ptr)}}",
        TAKE
    );
    with_facts(&code, |facts| {
        let call = fold_call_key(facts, "detach");
        let proof = super::fold_call::certify(
            facts,
            &call,
            0,
            &["Node::field0@d0".into()].into_iter().collect(),
        )
        .unwrap();
        let live = super::fold_permission::requirements(facts, &proof).unwrap();
        assert!(live.kind_keys.contains(&"Holder::field0@d0".into()));
        assert!(live.kind_keys.contains(&"Node::field0@d0".into()));
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let metadata = snapshot.metadata.facts();
        assert!(
            metadata.ownership_asts.is_empty()
                && metadata.slot_refs.is_empty()
                && metadata.guards.is_empty()
        );
        let keys = snapshot.metadata.slot_keys.iter().cloned().collect();
        let aliases = snapshot.metadata.guard_aliases.iter().copied().collect();
        assert_eq!(
            super::fold_permission::requirements_metadata(&metadata, &proof, &aliases, &keys),
            Ok(live)
        );
        let mut missing_key = keys.clone();
        assert!(missing_key.remove("Node::field0@d0"));
        assert_eq!(
            super::fold_permission::requirements_metadata(
                &metadata,
                &proof,
                &aliases,
                &missing_key
            ),
            Err("fold kind key has no native slot".into()),
            "accepted slot vocabulary must include the descendant field"
        );
        let mut missing_alias = aliases.clone();
        missing_alias.remove(&proof.internal.required_guards[0].0);
        assert!(
            super::fold_permission::requirements_metadata(&metadata, &proof, &missing_alias, &keys)
                .unwrap_err()
                .starts_with("fold proof no longer qualifies:")
        );
    });
}

#[test]
fn gf07_one_cell_call_declares_exact_pending_fold_without_removing_matches() {
    with_facts(TYPES, |facts| {
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let json = serde_json::to_value(&snapshot.metadata).unwrap();
        let declarations = json["fold_declarations"]
            .as_array()
            .expect("new-frame fold declaration inventory, even when empty");
        assert_eq!(declarations.len(), 1);
        let row = &declarations[0];
        let boundary_id = row["boundary"].as_u64().unwrap() as usize;
        let guard: super::facts::EquationId = serde_json::from_value(row["guard"].clone()).unwrap();
        let boundary = facts
            .boundary_substitutions
            .iter()
            .find(|b| b.ordinal == boundary_id)
            .unwrap();
        assert_eq!(boundary.callee.as_deref(), Some("identity"));
        assert_eq!(boundary.argument_index, Some(0));
        assert_eq!(boundary.matched.len(), 1);
        assert_eq!(boundary.unmatched_formal_vars.len(), 2);
        let equation = facts
            .equations
            .iter()
            .find(|e| e.point.construction == guard.construction && e.ordinal == guard.ordinal)
            .unwrap();
        assert_eq!(equation.point, boundary.point);
        assert_eq!(equation.operation, "guarded-fold-call");
        assert!(equation.variables.is_empty());
        use super::super::ownership_boundary::Variables;
        let (
            Variables::UseDef {
                use_var: a,
                def_var: b,
            },
            Variables::UseDef {
                use_var: c,
                def_var: d,
            },
        ) = (&boundary.matched[0].actual, &boundary.matched[0].formal)
        else {
            panic!("native consuming pair")
        };
        for variables in [[*c, *a], [*d, *b]] {
            assert!(
                facts.equations.iter().any(|e| e.point == boundary.point
                    && e.operation == "equal"
                    && e.variables == variables),
                "ordinary boundary equality retained"
            );
        }
        let rebuilt =
            super::snapshot::Metadata::from_facts(&snapshot.metadata.facts(), &snapshot.matched);
        assert_eq!(
            serde_json::to_value(rebuilt).unwrap()["fold_declarations"],
            json["fold_declarations"]
        );
        snapshot.validate().unwrap();
    });
}

#[test]
fn gf07_fully_matched_call_has_an_explicit_empty_fold_inventory() {
    with_facts(
        r#"
pub struct Node{child:*mut Node}
pub unsafe fn identity(node:*mut Node)->*mut Node{node}
pub unsafe fn caller(node:*mut Node)->*mut Node{identity(node)}
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            assert_eq!(
                serde_json::to_value(&snapshot.metadata).unwrap()["fold_declarations"],
                serde_json::json!([]),
                "full matches need no fold selector"
            );
        },
    );
}

#[test]
fn gf07_joint_declaration_marker_alias_omission_keeps_boundary_denominator() {
    with_facts(TYPES, |facts| {
        let mut bad = facts.clone();
        let declaration = bad.fold_declarations.as_mut().unwrap().pop().unwrap();
        bad.equations.retain(|e| {
            (e.point.construction, e.ordinal)
                != (declaration.guard.construction, declaration.guard.ordinal)
        });
        let mut aliases = super::matched::guard_aliases(&bad.guards);
        aliases.remove(&declaration.guard);
        assert_eq!(
            super::fold_declaration::validate(&bad, &aliases),
            Err("fold declaration coverage incomplete".into())
        );
    });
}

#[test]
fn gf07_pending_marker_cannot_claim_historical_unavailability() {
    with_facts(TYPES, |facts| {
        let mut bad = facts.clone();
        bad.fold_declarations = None;
        assert_eq!(
            super::fold_declaration::validate(&bad, &super::matched::guard_aliases(&bad.guards)),
            Err("fold declarations unavailable with marker".into())
        );
    });
}

#[test]
fn gf07_pending_selection_requires_complete_false_valuations() {
    with_facts(TYPES, |facts| {
        let guard = facts.fold_declarations.as_ref().unwrap()[0].guard;
        let aliases = super::matched::guard_aliases(&facts.guards);
        assert_eq!(
            super::fold_declaration::validate_selection(facts, &aliases, Some(&[(guard, false)])),
            Ok(())
        );
        assert_eq!(
            super::fold_declaration::validate_selection(facts, &aliases, None),
            Err("fold selection availability differs".into())
        );
        assert_eq!(
            super::fold_declaration::validate_selection(facts, &aliases, Some(&[])),
            Err("fold selection coverage differs".into())
        );
        assert_eq!(
            super::fold_declaration::validate_selection(facts, &aliases, Some(&[(guard, true)])),
            Err("pending fold selected without closure".into())
        );
    });
}
