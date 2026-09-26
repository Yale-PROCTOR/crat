//! Pending traversal call/return evidence. Discovery alone grants no call role.

use serde::{Deserialize, Serialize};

use super::{
    facts::{EquationId, Facts},
    matched::CallKey,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Candidate {
    pub(crate) call: CallKey,
    pub(crate) receiver_boundary: usize,
    pub(crate) argument_boundary: usize,
    pub(crate) parameter: u32,
    /// One actual predicate, shared by receiver and argument alternatives.
    pub(crate) guard: EquationId,
}

/// Exact pointer value borrowed by a call, distinct from its MIR argument proxy.
/// Projected admission is limited to one independently recorded pointer field.
pub(crate) struct InputTarget {
    pub(crate) place: super::super::ownership_access::PlaceSyntax,
    pub(crate) kind_key: String,
    pub(crate) parent_key: Option<String>,
}

pub(crate) fn input_target(
    facts: &Facts,
    proof: &super::traversal_correspondence::Proof,
) -> Option<InputTarget> {
    use super::super::{export::ProjKey, ownership_access::PlaceSyntax};
    let call = &proof.candidate.call;
    let consume = facts.consumes.iter().find(|c| {
        c.point.construction == call.construction && Some(c.ordinal) == proof.argument_consume
    })?;
    let place = PlaceSyntax {
        local: consume.local,
        projection: consume.projection.clone(),
    };
    let parent = format!("{}::_{}@d0", call.caller, consume.local);
    if place.projection.is_empty() {
        return facts
            .raw_pointer_heads
            .iter()
            .any(|h| h.function == call.caller && h.local == consume.local)
            .then_some(InputTarget {
                place,
                kind_key: parent,
                parent_key: None,
            });
    }
    if !matches!(
        place.projection.as_slice(),
        [ProjKey::Field(_)] | [ProjKey::Deref, ProjKey::Field(_)]
    ) {
        return None;
    }
    let load = one(facts.field_support_inputs.loads.iter().filter(|l| {
        l.direct_projection
            && !l.shared_reference_root
            && l.site.function == call.caller
            && Some(l.site.block) == consume.point.block
            && Some(l.site.statement) == consume.point.statement
            && l.site.place == place
    }))?;
    let parent_key = matches!(place.projection.first(), Some(ProjKey::Deref)).then_some(parent);
    Some(InputTarget {
        place,
        kind_key: load.site.field_key.clone(),
        parent_key,
    })
}

/// Preliminary syntax only; exact return/phi and lifetime proof is deferred
/// until all function bodies exist. Every declared predicate is held false.
pub(crate) fn preliminary(facts: &Facts, function: &str) -> Option<u32> {
    let reader = facts
        .reader_plan
        .functions
        .iter()
        .find(|r| r.function == function)?;
    let [parameter] = reader.returned_parameters.as_slice() else { return None };
    facts
        .reader_plan
        .candidates
        .iter()
        .any(|c| c.function == function && c.origin_parameter == *parameter)
        .then_some(*parameter)
}
fn one<T>(items: impl IntoIterator<Item = T>) -> Option<T> {
    let mut i = items.into_iter();
    let x = i.next()?;
    i.next().is_none().then_some(x)
}

pub(crate) fn guard_for(
    facts: &Facts,
    boundary: &super::super::ownership_boundary::Substitution,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
) -> Option<EquationId> {
    use super::super::ownership_boundary::{LicensingRole, Role};
    if boundary.licensing_role != LicensingRole::TraversalBorrow
        || !matches!(boundary.role, Role::CallArgument | Role::ReturnReceiver)
    {
        return None;
    }
    let function = boundary.point.function.as_ref()?;
    let callee = boundary.callee.as_ref()?;
    preliminary(facts, callee)?;
    let source = one(facts.source_occurrences.get(function)?.iter().filter(|s| {
        boundary.point.block == Some(s.site.block)
            && boundary.point.statement == Some(s.site.statement)
    }))?;
    if source.callee.as_ref()
        != Some(&super::super::origin_evidence::SourceCallee::Local(
            callee.clone(),
        ))
    {
        return None;
    }
    let decl = one(facts.equations.iter().filter(|e| {
        e.point == boundary.point && e.operation == "guarded-traversal-call" && e.validate().is_ok()
    }))?;
    let id = EquationId {
        construction: decl.point.construction,
        ordinal: decl.ordinal,
    };
    (aliases.get(&id) == Some(&id)).then_some(id)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ViewError {
    Boundary {
        call: CallKey,
    },
    Components {
        call: CallKey,
        operation: String,
        expected: Vec<Vec<u32>>,
        observed: Vec<(EquationId, Vec<u32>)>,
    },
    OldZero {
        call: CallKey,
        var: u32,
    },
}
pub(crate) fn validate_views(
    facts: &Facts,
    candidate: &Candidate,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
) -> Result<(), ViewError> {
    use std::collections::BTreeSet;

    use super::super::{ownership_boundary::Window, ownership_occurrence::Availability::Present};
    let failure = || ViewError::Boundary {
        call: candidate.call.clone(),
    };
    let row = |ordinal| {
        one(facts.boundary_substitutions.iter().filter(|b| {
            b.point.construction == candidate.call.construction && b.ordinal == ordinal
        }))
    };
    let receiver = row(candidate.receiver_boundary).ok_or_else(failure)?;
    let argument = row(candidate.argument_boundary).ok_or_else(failure)?;
    if receiver.point != argument.point
        || guard_for(facts, receiver, aliases) != Some(candidate.guard)
        || guard_for(facts, argument, aliases) != Some(candidate.guard)
    {
        return Err(failure());
    }
    let (
        Present(Window::UseDef {
            use_start: r0,
            use_end: r1,
            def_start: r2,
            def_end: r3,
        }),
        Present(Window::Single { start: t0, end: t1 }),
        Present(Window::UseDef {
            use_start: a0,
            use_end: a1,
            def_start: a2,
            def_end: a3,
        }),
    ) = (&receiver.actual, &receiver.formal, &argument.actual)
    else {
        return Err(failure());
    };
    if r1 - r0 != r3 - r2 || a1 - a0 != a3 - a2 {
        return Err(failure());
    }
    let formal = argument
        .reference_peel
        .as_ref()
        .map(|p| &p.original_formal)
        .or_else(|| match &argument.formal {
            Present(w) => Some(w),
            _ => None,
        })
        .ok_or_else(failure)?;
    let Window::UseDef {
        use_start: p0,
        use_end: p1,
        def_start: p2,
        def_end: p3,
    } = formal
    else {
        return Err(failure());
    };
    let sets = [
        (
            "guarded-traversal-view-zero",
            (*r2..*r3)
                .chain(*t0..*t1)
                .map(|v| vec![v])
                .collect::<BTreeSet<_>>(),
        ),
        (
            "guarded-traversal-frame",
            (*a0..*a1).zip(*a2..*a3).map(|(a, b)| vec![a, b]).collect(),
        ),
        (
            "guarded-traversal-formal-zero",
            (*p0..*p1).chain(*p2..*p3).map(|v| vec![v]).collect(),
        ),
    ];
    for (operation, expected) in sets {
        let rows: Vec<_> = facts
            .equations
            .iter()
            .filter(|e| e.point == receiver.point && e.operation == operation)
            .collect();
        let actual: BTreeSet<_> = rows.iter().map(|e| e.variables.clone()).collect();
        if expected.is_empty()
            || actual != expected
            || rows.len() != actual.len()
            || rows.iter().any(|e| {
                e.validate().is_err()
                    || aliases.get(&EquationId {
                        construction: e.point.construction,
                        ordinal: e.ordinal,
                    }) != Some(&candidate.guard)
            })
        {
            return Err(ViewError::Components {
                call: candidate.call.clone(),
                operation: operation.into(),
                expected: expected.into_iter().collect(),
                observed: rows
                    .iter()
                    .map(|e| {
                        (
                            EquationId {
                                construction: e.point.construction,
                                ordinal: e.ordinal,
                            },
                            e.variables.clone(),
                        )
                    })
                    .collect(),
            });
        }
    }
    for var in *r0..*r1 {
        if !facts.equations.iter().any(|e| {
            e.point == receiver.point
                && e.operation == "assume"
                && e.value == Some(false)
                && e.variables == [var]
                && e.guard.is_none()
        }) {
            return Err(ViewError::OldZero {
                call: candidate.call.clone(),
                var,
            });
        }
    }
    Ok(())
}

pub(crate) fn discover(facts: &Facts) -> Vec<Candidate> {
    discover_metadata(facts, &super::matched::guard_aliases(&facts.guards))
}
pub(crate) fn discover_metadata(
    facts: &Facts,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
) -> Vec<Candidate> {
    use super::super::{
        origin_evidence::SourceCallee,
        ownership_boundary::{Role, Variables},
        ownership_occurrence::Availability::Present,
    };
    facts
        .equations
        .iter()
        .filter(|e| e.operation == "guarded-traversal-call")
        .filter_map(|decl| {
            if decl.validate().is_err() {
                return None;
            }
            let function = decl.point.function.as_ref()?;
            let original = one(facts
                .source_occurrences
                .get(function)?
                .iter()
                .filter(|row| {
                    decl.point.block == Some(row.site.block)
                        && decl.point.statement == Some(row.site.statement)
                }))?;
            let Some(SourceCallee::Local(callee)) = &original.callee else { return None };
            let parameter = preliminary(facts, callee)?;
            let guard = EquationId {
                construction: decl.point.construction,
                ordinal: decl.ordinal,
            };
            if aliases.get(&guard) != Some(&guard) {
                return None;
            }
            let receiver = one(facts.boundary_substitutions.iter().filter(|b| {
                b.point == decl.point
                    && b.role == Role::ReturnReceiver
                    && b.callee.as_ref() == Some(callee)
            }))?;
            let argument = one(facts.boundary_substitutions.iter().filter(|b| {
                b.point == decl.point
                    && b.role == Role::CallArgument
                    && b.callee.as_ref() == Some(callee)
                    && b.formal_local == Some(parameter)
            }))?;
            if receiver.matched.is_empty()
                || argument.matched.is_empty()
                || !matches!(receiver.actual_occurrence, Present(_))
                || !matches!(argument.actual_occurrence, Present(_))
                || !matches!(argument.call_arg_registration, Present(_))
            {
                return None;
            }
            let mut expected = std::collections::BTreeSet::new();
            for pair in &receiver.matched {
                let (Variables::UseDef { use_var, def_var }, Variables::Single { var }) =
                    (&pair.actual, &pair.formal)
                else {
                    return None;
                };
                if !facts.equations.iter().any(|e| {
                    e.point == decl.point
                        && e.operation == "assume"
                        && e.value == Some(false)
                        && e.variables == [*use_var]
                }) {
                    return None;
                }
                expected.insert(("guarded-traversal-receiver-legacy", vec![*def_var, *var]));
            }
            for pair in &argument.matched {
                let (
                    Variables::UseDef {
                        use_var: a,
                        def_var: b,
                    },
                    Variables::UseDef {
                        use_var: c,
                        def_var: d,
                    },
                ) = (&pair.actual, &pair.formal)
                else {
                    return None;
                };
                expected.insert(("guarded-traversal-argument-legacy", vec![*c, *a, *d, *b]));
            }
            let rows: Vec<_> = facts
                .equations
                .iter()
                .filter(|e| {
                    e.point == decl.point
                        && matches!(
                            e.operation.as_str(),
                            "guarded-traversal-receiver-legacy"
                                | "guarded-traversal-argument-legacy"
                        )
                })
                .collect();
            let actual: std::collections::BTreeSet<_> = rows
                .iter()
                .map(|e| (e.operation.as_str(), e.variables.clone()))
                .collect();
            if rows.len() != actual.len()
                || actual != expected
                || rows.iter().any(|e| {
                    e.validate().is_err()
                        || aliases.get(&EquationId {
                            construction: e.point.construction,
                            ordinal: e.ordinal,
                        }) != Some(&guard)
                })
            {
                return None;
            }
            let candidate = Candidate {
                call: CallKey {
                    construction: guard.construction,
                    caller: function.clone(),
                    block: decl.point.block?,
                    statement: decl.point.statement?,
                    callee: callee.clone(),
                },
                receiver_boundary: receiver.ordinal,
                argument_boundary: argument.ordinal,
                parameter,
                guard,
            };
            validate_views(facts, &candidate, aliases).ok()?;
            Some(candidate)
        })
        .collect()
}

/// Exact ownership-valuation subset needed to check both call arms. These
/// run-local Vars are interpreted only in the accepted snapshot namespace.
pub(crate) fn valuation_nodes(
    facts: &Facts,
    candidates: &[Candidate],
) -> Result<std::collections::BTreeSet<super::transport::Node>, String> {
    use super::super::{ownership_boundary::Window, ownership_occurrence::Availability::Present};
    let mut nodes = std::collections::BTreeSet::new();
    for candidate in candidates {
        for ordinal in [candidate.receiver_boundary, candidate.argument_boundary] {
            let row = one(facts.boundary_substitutions.iter().filter(|b| {
                b.point.construction == candidate.call.construction && b.ordinal == ordinal
            }))
            .ok_or("traversal valuation boundary missing")?;
            let (Present(actual), Present(formal)) = (&row.actual, &row.formal) else {
                return Err("traversal valuation window missing".into());
            };
            for window in [
                Some(actual),
                Some(formal),
                row.reference_peel.as_ref().map(|p| &p.original_formal),
            ]
            .into_iter()
            .flatten()
            {
                let ranges = match window {
                    Window::Single { start, end } => vec![*start..*end],
                    Window::UseDef {
                        use_start,
                        use_end,
                        def_start,
                        def_end,
                    } => vec![*use_start..*use_end, *def_start..*def_end],
                };
                for range in ranges {
                    nodes.extend(range.map(|var| super::transport::Node {
                        construction: candidate.call.construction,
                        var,
                    }));
                }
            }
        }
    }
    Ok(nodes)
}

pub(crate) fn validate_valuation(
    facts: &Facts,
    candidates: &[Candidate],
    guards: &std::collections::BTreeMap<EquationId, bool>,
    observed: &[(super::transport::Node, bool)],
) -> Result<(), String> {
    use super::super::{
        ownership_boundary::{Variables, Window},
        ownership_occurrence::Availability::Present,
    };
    let required = valuation_nodes(facts, candidates)?;
    let values: std::collections::BTreeMap<_, _> = observed.iter().copied().collect();
    if values.len() != observed.len()
        || values
            .keys()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            != required
    {
        return Err("traversal ownership valuation coverage differs".into());
    }
    for candidate in candidates {
        let call = &candidate.call;
        let value = |var| {
            values
                .get(&super::transport::Node {
                    construction: call.construction,
                    var,
                })
                .copied()
                .ok_or_else(|| "traversal ownership value missing".to_owned())
        };
        let receiver = one(facts.boundary_substitutions.iter().filter(|b| {
            b.point.construction == call.construction && b.ordinal == candidate.receiver_boundary
        }))
        .ok_or("traversal receiver valuation missing")?;
        let argument = one(facts.boundary_substitutions.iter().filter(|b| {
            b.point.construction == call.construction && b.ordinal == candidate.argument_boundary
        }))
        .ok_or("traversal argument valuation missing")?;
        let Present(Window::UseDef {
            use_start: r0,
            use_end: r1,
            def_start: r2,
            def_end: r3,
        }) = &receiver.actual
        else {
            return Err("traversal receiver window missing".into());
        };
        for var in *r0..*r1 {
            if value(var)? {
                return Err(format!(
                    "traversal receiver old-zero valuation mismatch: {call:?}"
                ));
            }
        }
        if *guards
            .get(&candidate.guard)
            .ok_or("traversal guard valuation missing")?
        {
            let Present(Window::Single { start: t0, end: t1 }) = &receiver.formal else {
                return Err("traversal return window missing".into());
            };
            for var in (*r2..*r3).chain(*t0..*t1) {
                if value(var)? {
                    return Err(format!(
                        "traversal returned view valuation mismatch: {call:?}"
                    ));
                }
            }
            let Present(Window::UseDef {
                use_start: a0,
                use_end: a1,
                def_start: a2,
                def_end: a3,
            }) = &argument.actual
            else {
                return Err("traversal actual window missing".into());
            };
            for (a, b) in (*a0..*a1).zip(*a2..*a3) {
                if value(a)? != value(b)? {
                    return Err(format!(
                        "traversal caller frame valuation mismatch: {call:?}"
                    ));
                }
            }
            let formal = argument
                .reference_peel
                .as_ref()
                .map(|p| &p.original_formal)
                .or_else(|| match &argument.formal {
                    Present(w) => Some(w),
                    _ => None,
                })
                .ok_or("traversal formal window missing")?;
            let Window::UseDef {
                use_start: p0,
                use_end: p1,
                def_start: p2,
                def_end: p3,
            } = formal
            else {
                return Err("traversal formal window shape".into());
            };
            for var in (*p0..*p1).chain(*p2..*p3) {
                if value(var)? {
                    return Err(format!(
                        "traversal formal view valuation mismatch: {call:?}"
                    ));
                }
            }
        } else {
            for pair in &receiver.matched {
                let (Variables::UseDef { def_var, .. }, Variables::Single { var }) =
                    (&pair.actual, &pair.formal)
                else {
                    return Err("traversal receiver pair shape".into());
                };
                if value(*def_var)? != value(*var)? {
                    return Err(format!(
                        "traversal legacy receiver valuation mismatch: {call:?}"
                    ));
                }
            }
            for pair in &argument.matched {
                let (
                    Variables::UseDef {
                        use_var: a,
                        def_var: b,
                    },
                    Variables::UseDef {
                        use_var: c,
                        def_var: d,
                    },
                ) = (&pair.actual, &pair.formal)
                else {
                    return Err("traversal argument pair shape".into());
                };
                if value(*a)? != value(*c)? || value(*b)? != value(*d)? {
                    return Err(format!(
                        "traversal legacy argument valuation mismatch: {call:?}"
                    ));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{
        super::{
            super::{
                origin_evidence::SourceCallee,
                ownership_boundary::{LicensingRole, Role, Variables},
                ownership_occurrence::Availability,
            },
            graph_tests::with_facts,
            matched,
        },
        *,
    };

    const NODE: &str = "pub struct Node {left:*mut Node, right:*mut Node, value:i32}";
    const MINIMUM: &str = r#"
pub unsafe fn minimum(mut node:*mut Node)->*mut Node {
    while !(*node).left.is_null() {node=(*node).left;}
    node
}
"#;
    const CALLER: &str = r#"
pub unsafe fn caller(node:*mut Node)->*mut Node {let result=minimum(node);result}
"#;

    fn check_order(caller_first: bool) {
        let (first, last) = if caller_first {
            (CALLER, MINIMUM)
        } else {
            (MINIMUM, CALLER)
        };
        let code = format!("{NODE}\n{first}\n{last}");
        with_facts(&code, move |facts| {
            assert_eq!(
                facts.constructions, 1,
                "call ordering must not cause re-emission"
            );
            let candidates = discover(facts);
            let [candidate] = candidates.as_slice() else {
                panic!(
                    "one exact pending traversal call required, caller_first={caller_first}: {candidates:?}"
                )
            };
            let calls: Vec<_> = facts.source_occurrences["caller"]
                .iter()
                .filter(|row| row.callee == Some(SourceCallee::Local("minimum".into())))
                .collect();
            let [call] = calls.as_slice() else { panic!("one original call occurrence required") };
            assert_eq!(
                candidate.call,
                CallKey {
                    construction: candidate.guard.construction,
                    caller: call.site.function.clone(),
                    block: call.site.block,
                    statement: call.site.statement,
                    callee: "minimum".into(),
                }
            );
            let scope = |point: &super::super::super::ownership_evidence::Point| {
                point.construction == candidate.call.construction
                    && point.function.as_ref() == Some(&candidate.call.caller)
                    && point.block == Some(candidate.call.block)
                    && point.statement == Some(candidate.call.statement)
            };
            let boundary = |ordinal, role| {
                let rows: Vec<_> = facts
                    .boundary_substitutions
                    .iter()
                    .filter(|row| {
                        row.ordinal == ordinal
                            && scope(&row.point)
                            && row.role == role
                            && row.callee.as_ref() == Some(&candidate.call.callee)
                    })
                    .collect();
                assert_eq!(rows.len(), 1, "exact call boundary {ordinal}/{role:?}");
                rows[0]
            };
            let receiver = boundary(candidate.receiver_boundary, Role::ReturnReceiver);
            let argument = boundary(candidate.argument_boundary, Role::CallArgument);
            assert_ne!(candidate.receiver_boundary, candidate.argument_boundary);
            assert_eq!(argument.formal_local, Some(candidate.parameter));
            assert_eq!(
                argument.argument_index.map(|i| i as u32 + 1),
                Some(candidate.parameter)
            );
            assert!(matches!(
                receiver.actual_occurrence,
                Availability::Present(_)
            ));
            assert!(matches!(
                argument.actual_occurrence,
                Availability::Present(_)
            ));
            assert!(matches!(
                argument.call_arg_registration,
                Availability::Present(_)
            ));
            assert!(
                receiver.unmatched_actual_vars.is_empty()
                    && receiver.unmatched_formal_vars.is_empty()
            );
            assert!(
                argument.unmatched_actual_vars.is_empty()
                    && argument.unmatched_formal_vars.is_empty()
            );
            let aliases = matched::guard_aliases(&facts.guards);
            let declared: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| scope(&row.point) && row.operation == "guarded-traversal-call")
                .collect();
            assert_eq!(
                declared.len(),
                1,
                "receiver and argument share one declaration"
            );
            assert_eq!(
                EquationId {
                    construction: declared[0].point.construction,
                    ordinal: declared[0].ordinal
                },
                candidate.guard
            );
            assert!(declared[0].variables.is_empty());
            let mut expected_receiver = BTreeSet::new();
            for pair in &receiver.matched {
                let (Variables::UseDef { use_var, def_var }, Variables::Single { var }) =
                    (&pair.actual, &pair.formal)
                else {
                    panic!("exact receiver/return window required")
                };
                expected_receiver.insert(vec![*def_var, *var]);
                assert!(
                    facts.equations.iter().any(|row| scope(&row.point)
                        && row.operation == "assume"
                        && row.value == Some(false)
                        && row.variables == [*use_var]
                        && row.guard.is_none()),
                    "receiver old-zero stays unconditional: {:?}, old={use_var}",
                    candidate.call
                );
            }
            let mut expected_argument = BTreeSet::new();
            for pair in &argument.matched {
                let (
                    Variables::UseDef {
                        use_var: actual_pre,
                        def_var: actual_post,
                    },
                    Variables::UseDef {
                        use_var: formal_pre,
                        def_var: formal_post,
                    },
                ) = (&pair.actual, &pair.formal)
                else {
                    panic!("full input/output call correspondence required")
                };
                expected_argument.insert(vec![
                    *formal_pre,
                    *actual_pre,
                    *formal_post,
                    *actual_post,
                ]);
            }
            for (operation, expected) in [
                ("guarded-traversal-receiver-legacy", expected_receiver),
                ("guarded-traversal-argument-legacy", expected_argument),
            ] {
                assert!(!expected.is_empty());
                let rows: Vec<_> = facts
                    .equations
                    .iter()
                    .filter(|row| scope(&row.point) && row.operation == operation)
                    .collect();
                let actual: BTreeSet<_> = rows.iter().map(|row| row.variables.clone()).collect();
                assert_eq!(rows.len(), actual.len(), "duplicate false-arm tuple");
                assert_eq!(
                    actual, expected,
                    "false arm preserves exact baseline linkage: {operation}"
                );
                for row in rows {
                    let id = EquationId {
                        construction: row.point.construction,
                        ordinal: row.ordinal,
                    };
                    assert_eq!(
                        aliases.get(&id),
                        Some(&candidate.guard),
                        "one predicate at {id:?}"
                    );
                }
            }
        });
    }

    #[test]
    fn c07_traversal_call_caller_first_records_one_exact_pending_guard() {
        check_order(true);
    }

    #[test]
    fn c07_traversal_call_caller_last_records_one_exact_pending_guard() {
        check_order(false);
    }

    // True-arm families enumerate complete recorded windows, independently of
    // matched component counts: view-zero(var), frame(before, after), and
    // formal-zero(var). The existing pending-hold control keeps their guard false.
    fn check_true_arm_windows(caller_first: bool) {
        use super::super::super::ownership_boundary::Window;

        let (first, last) = if caller_first {
            (CALLER, MINIMUM)
        } else {
            (MINIMUM, CALLER)
        };
        let code = format!("{NODE}\n{first}\n{last}");
        with_facts(&code, move |facts| {
            assert_eq!(facts.constructions, 1);
            let candidates = discover(facts);
            let [candidate] = candidates.as_slice() else {
                panic!("one exact pending traversal call")
            };
            let find_boundary = |ordinal| {
                let rows: Vec<_> = facts
                    .boundary_substitutions
                    .iter()
                    .filter(|row| {
                        row.point.construction == candidate.call.construction
                            && row.ordinal == ordinal
                    })
                    .collect();
                assert_eq!(rows.len(), 1);
                rows[0]
            };
            let receiver = find_boundary(candidate.receiver_boundary);
            let argument = find_boundary(candidate.argument_boundary);
            assert_eq!(receiver.point, argument.point);
            let Availability::Present(Window::UseDef {
                use_start: r0,
                use_end: r1,
                def_start: r2,
                def_end: r3,
            }) = &receiver.actual
            else {
                panic!("complete receiver consume window")
            };
            let Availability::Present(Window::Single { start: t0, end: t1 }) = &receiver.formal
            else {
                panic!("complete return signature window")
            };
            let Availability::Present(Window::UseDef {
                use_start: a0,
                use_end: a1,
                def_start: a2,
                def_end: a3,
            }) = &argument.actual
            else {
                panic!("complete actual argument consume window")
            };
            let formal = argument
                .reference_peel
                .as_ref()
                .map(|peel| &peel.original_formal)
                .unwrap_or_else(|| {
                    let Availability::Present(formal) = &argument.formal else {
                        panic!("formal window")
                    };
                    formal
                });
            let Window::UseDef {
                use_start: p0,
                use_end: p1,
                def_start: p2,
                def_end: p3,
            } = formal
            else {
                panic!("full pre-peel formal input/output window")
            };
            assert_eq!(r1 - r0, r3 - r2);
            assert_eq!(a1 - a0, a3 - a2);
            assert_eq!(p1 - p0, p3 - p2);
            let expected_views: BTreeSet<_> =
                (*r2..*r3).chain(*t0..*t1).map(|var| vec![var]).collect();
            let expected_frames: BTreeSet<_> = (*a0..*a1)
                .zip(*a2..*a3)
                .map(|(before, after)| vec![before, after])
                .collect();
            let expected_formals: BTreeSet<_> =
                (*p0..*p1).chain(*p2..*p3).map(|var| vec![var]).collect();
            let aliases = matched::guard_aliases(&facts.guards);
            for (operation, expected) in [
                ("guarded-traversal-view-zero", expected_views),
                ("guarded-traversal-frame", expected_frames),
                ("guarded-traversal-formal-zero", expected_formals),
            ] {
                assert!(
                    !expected.is_empty(),
                    "non-vacuous complete window for {operation}"
                );
                let rows: Vec<_> = facts
                    .equations
                    .iter()
                    .filter(|row| row.point == receiver.point && row.operation == operation)
                    .collect();
                let actual: BTreeSet<_> = rows.iter().map(|row| row.variables.clone()).collect();
                assert_eq!(
                    actual, expected,
                    "true-arm complete-window coverage at {:?}, operation={operation}, caller_first={caller_first}",
                    candidate.call
                );
                assert_eq!(
                    rows.len(),
                    actual.len(),
                    "duplicate true-arm component at {:?}: {operation}",
                    candidate.call
                );
                for row in rows {
                    let id = EquationId {
                        construction: row.point.construction,
                        ordinal: row.ordinal,
                    };
                    assert!(
                        row.guard.is_some() && row.value.is_none(),
                        "guarded obligation, never an unconditional zero: {id:?}"
                    );
                    assert_eq!(
                        aliases.get(&id),
                        Some(&candidate.guard),
                        "true and false arms share one exact guard: {id:?}"
                    );
                }
            }
            for var in *r0..*r1 {
                assert!(
                    facts.equations.iter().any(|row| row.point == receiver.point
                        && row.operation == "assume"
                        && row.value == Some(false)
                        && row.variables == [var]
                        && row.guard.is_none()),
                    "full receiver-old-zero remains unconditional: {:?}, var={var}",
                    candidate.call
                );
            }
        });
    }

    #[test]
    fn c07_traversal_call_true_arm_caller_first_covers_full_windows() {
        check_true_arm_windows(true);
    }

    #[test]
    fn c07_traversal_call_true_arm_caller_last_covers_full_windows() {
        check_true_arm_windows(false);
    }

    #[test]
    fn c07_traversal_call_identity_retains_ordinary_owning_capable_linkage() {
        with_facts(
            r#"
pub unsafe fn identity(p:*mut i32)->*mut i32 {p}
pub unsafe fn caller(p:*mut i32)->*mut i32 {identity(p)}
"#,
            |facts| {
                assert_eq!(facts.constructions, 1);
                assert!(
                    discover(facts).is_empty(),
                    "identity is not a borrowed traversal call"
                );
                assert!(
                    !facts
                        .equations
                        .iter()
                        .any(|e| e.operation.starts_with("guarded-traversal-"))
                );
                let rows: Vec<_> = facts
                    .boundary_substitutions
                    .iter()
                    .filter(|row| {
                        row.point.function.as_deref() == Some("caller")
                            && row.callee.as_deref() == Some("identity")
                            && matches!(row.role, Role::CallArgument | Role::ReturnReceiver)
                    })
                    .collect();
                assert_eq!(rows.len(), 2);
                for row in rows {
                    assert_ne!(row.licensing_role, LicensingRole::Borrowed);
                    for pair in &row.matched {
                        let Variables::UseDef {
                            use_var: actual_pre,
                            def_var: actual_post,
                        } = pair.actual
                        else {
                            panic!("actual call window required")
                        };
                        let expected = match pair.formal {
                            Variables::Single { var } => vec![vec![actual_post, var]],
                            Variables::UseDef { use_var, def_var } => {
                                vec![vec![use_var, actual_pre], vec![def_var, actual_post]]
                            }
                        };
                        for variables in expected {
                            assert!(
                                facts.equations.iter().any(|e| e.point == row.point
                                    && e.operation == "equal"
                                    && e.variables == variables
                                    && e.guard.is_none()),
                                "ordinary equality retained: {:?}/{variables:?}",
                                row.point
                            );
                        }
                    }
                }
            },
        );
    }
    #[test]
    fn c07_traversal_call_pending_guard_is_hard_false_without_a_query() {
        let code = format!("{NODE}\n{CALLER}\n{MINIMUM}");
        super::super::graph_tests::with_solver_facts(&code, |facts, solver, _| {
            let candidate = discover(facts).pop().unwrap();
            let binding = facts
                .guards
                .iter()
                .find(|b| b.equation == candidate.guard)
                .unwrap();
            let hold = if let Some(tracker) = solver.tracker() {
                let tracks: Vec<_> = tracker
                    .tracks()
                    .into_iter()
                    .filter(|track| {
                        tracker
                            .label_of(track)
                            .is_some_and(|label| label.ends_with("::own-traversal-pending"))
                    })
                    .collect();
                assert_eq!(
                    tracks.len(),
                    1,
                    "one typed pending hold per exact call guard"
                );
                z3::ast::Bool::or(&[!&tracks[0], !&binding.predicate])
            } else {
                !&binding.predicate
            };
            assert!(
                solver.optimize().get_assertions().contains(&hold),
                "pending traversal guard must be explicitly held by its mandatory clause: {:?}",
                candidate.guard
            );
            let declaration = facts
                .equations
                .iter()
                .find(|e| e.ordinal == candidate.guard.ordinal)
                .unwrap();
            let first_receiver = facts
                .equations
                .iter()
                .filter(|e| {
                    e.point == declaration.point
                        && e.operation == "guarded-traversal-receiver-legacy"
                })
                .map(|e| e.ordinal)
                .min()
                .unwrap();
            assert!(
                declaration.ordinal < first_receiver,
                "one guard exists before receiver emission"
            );
        });
    }
    #[test]
    fn c07_traversal_call_snapshot_and_missing_tuple_controls() {
        let code = format!("{NODE}\n{CALLER}\n{MINIMUM}");
        with_facts(&code, |facts| {
            let snapshot = super::super::snapshot::Snapshot::capture(facts, 0).unwrap();
            assert_eq!(snapshot.traversal_calls, discover(facts));
            assert_eq!(snapshot.traversal_calls.len(), 1);
            snapshot.validate().unwrap();
            let decoded: super::super::snapshot::Snapshot =
                serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
            decoded.validate().unwrap();
            let mut omitted = decoded.clone();
            omitted.traversal_calls.clear();
            assert!(omitted.validate().is_err());
            for operation in [
                "guarded-traversal-receiver-legacy",
                "guarded-traversal-argument-legacy",
            ] {
                let mut missing = facts.clone();
                let index = missing
                    .equations
                    .iter()
                    .position(|e| e.operation == operation)
                    .unwrap();
                let removed = missing.equations.remove(index);
                assert!(
                    discover(&missing).is_empty(),
                    "missing required {operation} tuple at {:?}/{}",
                    removed.point,
                    removed.ordinal
                );
            }
            let mut wrong = decoded;
            wrong.traversal_calls[0].receiver_boundary = wrong.traversal_calls[0].argument_boundary;
            assert!(wrong.validate().is_err());
        });
    }
    #[test]
    fn c07_traversal_call_view_components_reject_missing_or_wrong_guard_with_typed_reason() {
        let code = format!("{NODE}\n{CALLER}\n{MINIMUM}");
        with_facts(&code, |facts| {
            let candidate = discover(facts).pop().unwrap();
            let aliases = matched::guard_aliases(&facts.guards);
            validate_views(facts, &candidate, &aliases).unwrap();
            for operation in [
                "guarded-traversal-view-zero",
                "guarded-traversal-formal-zero",
                "guarded-traversal-frame",
            ] {
                let mut missing = facts.clone();
                let index = missing
                    .equations
                    .iter()
                    .position(|e| e.operation == operation)
                    .unwrap();
                let removed = missing.equations.remove(index);
                let error = validate_views(&missing, &candidate, &aliases).unwrap_err();
                assert!(
                    matches!(error,ViewError::Components{ref call,operation:ref op,..} if call==&candidate.call && op==operation),
                    "typed missing component: {error:?}; equation={:?}/{}",
                    removed.point,
                    removed.ordinal
                );
                let mut wrong = aliases.clone();
                let id = EquationId {
                    construction: removed.point.construction,
                    ordinal: removed.ordinal,
                };
                wrong.remove(&id);
                assert!(
                    matches!(
                        validate_views(facts, &candidate, &wrong),
                        Err(ViewError::Components { .. })
                    ),
                    "missing actual predicate binding for {id:?}"
                );
            }
            let receiver = facts
                .boundary_substitutions
                .iter()
                .find(|b| {
                    b.ordinal == candidate.receiver_boundary
                        && b.point.construction == candidate.call.construction
                })
                .unwrap();
            let Variables::UseDef { use_var, .. } = receiver.matched[0].actual else {
                unreachable!()
            };
            let mut missing = facts.clone();
            missing.equations.retain(|e| {
                !(e.point == receiver.point
                    && e.operation == "assume"
                    && e.value == Some(false)
                    && e.variables == [use_var])
            });
            assert_eq!(
                validate_views(&missing, &candidate, &aliases),
                Err(ViewError::OldZero {
                    call: candidate.call.clone(),
                    var: use_var
                })
            );
        });
    }
    #[test]
    fn c07_traversal_call_true_frames_are_local_and_legacy_edges_are_false_guarded() {
        let code = format!("{NODE}\n{CALLER}\n{MINIMUM}");
        with_facts(&code, |facts| {
            use super::super::transport::{CandidateGraph, Evidence, Rule};
            let candidate = discover(facts).pop().unwrap();
            let graph = CandidateGraph::build(facts);
            let cross:Vec<_>=graph.edges.iter().filter(|e|matches!(e.evidence,Evidence::Boundary{ordinal,..} if ordinal==candidate.argument_boundary||ordinal==candidate.receiver_boundary)).collect();
            assert!(!cross.is_empty());
            assert!(cross.iter().all(|e| {
                e.guard
                    .is_some_and(|g| g.binding == candidate.guard && !g.required)
            }));
            let frames: Vec<_> = graph
                .edges
                .iter()
                .filter(|e| matches!(e.evidence, Evidence::TraversalFrame(_)))
                .collect();
            assert!(!frames.is_empty());
            for edge in frames {
                assert_eq!(edge.rule, Rule::Frame);
                assert!(
                    edge.guard
                        .is_some_and(|g| g.binding == candidate.guard && g.required)
                );
            }
            assert!(
                graph
                    .borrowed_views
                    .iter()
                    .all(|view| view.guard.binding != candidate.guard),
                "pending traversal call invents no ownership-bearing borrowed return"
            );
        });
    }
    #[test]
    fn c07_traversal_call_native_reference_covers_prepeel_formal() {
        let code = format!(
            "{NODE}\n{}\n{MINIMUM}",
            CALLER.replace("node:*mut Node", "node:&mut Node")
        );
        with_facts(&code, |facts| {
            let candidate = discover(facts)
                .pop()
                .expect("native reference call candidate");
            let aliases = matched::guard_aliases(&facts.guards);
            validate_views(facts, &candidate, &aliases).unwrap();
            let argument = facts
                .boundary_substitutions
                .iter()
                .find(|b| {
                    b.ordinal == candidate.argument_boundary
                        && b.point.construction == candidate.call.construction
                })
                .unwrap();
            let peel = argument
                .reference_peel
                .as_ref()
                .expect("actual native reference peel");
            let Variables::UseDef { use_var, def_var } = peel.skipped else { unreachable!() };
            for var in [use_var, def_var] {
                let row = facts
                    .equations
                    .iter()
                    .find(|e| {
                        e.point == argument.point
                            && e.operation == "guarded-traversal-formal-zero"
                            && e.variables == [var]
                    })
                    .expect("skipped formal outer pair remains zero under the same guard");
                assert_eq!(
                    aliases.get(&EquationId {
                        construction: row.point.construction,
                        ordinal: row.ordinal
                    }),
                    Some(&candidate.guard)
                );
            }
        });
    }
}
