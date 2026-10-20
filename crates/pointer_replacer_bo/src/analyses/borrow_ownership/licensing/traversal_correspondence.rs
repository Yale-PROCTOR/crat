//! Late traversal/native correspondence. This metadata grants no selected borrow.

use serde::{Deserialize, Serialize};

use super::{facts::Facts, matched::CallKey, traversal_call, traversal_native, traversal_return};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Proof {
    pub(crate) candidate: traversal_call::Candidate,
    pub(crate) traversal: traversal_return::Proof,
    pub(crate) native: traversal_native::CallObservation,
    pub(crate) argument_registration: usize,
    /// The proxy may be erased, but this subset requires its underlying consume.
    pub(crate) argument_consume: Option<usize>,
    pub(crate) receiver_consume: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum HoldReason {
    NativeFlowsUnavailable,
    MissingCallObservation,
    AmbiguousCallObservation,
    CallIdentityMismatch,
    ArgumentCorrespondence,
    ReceiverConsumeMismatch,
    MissingReturnFlow,
    UnknownReturnOrigin,
    UnexpectedIncomingOrigin,
    CallerFlowAbsent,
    TraversalIncomplete,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Hold {
    pub(crate) call: CallKey,
    pub(crate) reason: HoldReason,
    pub(crate) boundary: Option<usize>,
    pub(crate) consume: Option<usize>,
}

fn one<T>(items: impl IntoIterator<Item = T>) -> Option<T> {
    let mut items = items.into_iter();
    let first = items.next()?;
    items.next().is_none().then_some(first)
}

pub(crate) fn certify(facts: &Facts, candidate: &traversal_call::Candidate) -> Result<Proof, Hold> {
    certify_metadata(
        facts,
        candidate,
        &super::matched::guard_aliases(&facts.guards),
    )
}
pub(crate) fn certify_metadata(
    facts: &Facts,
    candidate: &traversal_call::Candidate,
    aliases: &std::collections::BTreeMap<super::facts::EquationId, super::facts::EquationId>,
) -> Result<Proof, Hold> {
    use super::super::{
        origin_evidence::{OriginAvailability, SourceCallee},
        ownership_access::{Expression, OperandSyntax},
        ownership_boundary::{self, Role, Window},
        ownership_occurrence::Availability::Present,
    };
    let hold = |reason, boundary, consume| Hold {
        call: candidate.call.clone(),
        reason,
        boundary,
        consume,
    };
    let simple = |reason| hold(reason, None, None);
    let input = facts
        .traversal_native
        .as_ref()
        .filter(|i| i.status == traversal_native::Status::Observed)
        .ok_or_else(|| simple(HoldReason::NativeFlowsUnavailable))?;
    let observations: Vec<_> = input
        .calls
        .iter()
        .filter(|row| row.call == candidate.call)
        .collect();
    if observations.is_empty() {
        return Err(simple(HoldReason::MissingCallObservation));
    }
    if observations.len() != 1 || input.missing.iter().any(|m| m.call == candidate.call) {
        return Err(simple(HoldReason::AmbiguousCallObservation));
    }
    let native = observations[0];
    let call = &candidate.call;
    let source = one(facts
        .source_occurrences
        .get(&call.caller)
        .into_iter()
        .flatten()
        .filter(|r| {
            r.site.block == call.block
                && r.site.statement == call.statement
                && r.callee == Some(SourceCallee::Local(call.callee.clone()))
        }))
    .ok_or_else(|| simple(HoldReason::CallIdentityMismatch))?;
    let argument = one(facts.boundary_substitutions.iter().filter(|b| {
        b.point.construction == call.construction
            && b.ordinal == candidate.argument_boundary
            && b.role == Role::CallArgument
    }))
    .ok_or_else(|| simple(HoldReason::ArgumentCorrespondence))?;
    let receiver = one(facts.boundary_substitutions.iter().filter(|b| {
        b.point.construction == call.construction
            && b.ordinal == candidate.receiver_boundary
            && b.role == Role::ReturnReceiver
    }))
    .ok_or_else(|| simple(HoldReason::ReceiverConsumeMismatch))?;
    let receiver_id = match receiver.actual_occurrence {
        Present(id) => id,
        _ => {
            return Err(hold(
                HoldReason::ReceiverConsumeMismatch,
                Some(receiver.ordinal),
                None,
            ));
        }
    };
    let bad_receiver = || {
        hold(
            HoldReason::ReceiverConsumeMismatch,
            Some(receiver.ordinal),
            Some(receiver_id),
        )
    };
    let actual = one(facts
        .consumes
        .iter()
        .filter(|c| c.point.construction == call.construction && c.ordinal == receiver_id))
    .ok_or_else(bad_receiver)?;
    let roster_matches = |consume: &super::super::ownership_occurrence::Consumption| {
        let Some(roster) = one(facts.body_rosters.iter().filter(|r| {
            r.point.construction == consume.point.construction
                && r.point.function == consume.point.function
        })) else {
            return false;
        };
        let Present(base) = &consume.base else { return false };
        if !roster.consumes.iter().any(|r| {
            Some(r.block) == consume.point.block
                && Some(r.statement) == consume.point.statement
                && r.local == consume.local
                && Some(r.use_ssa) == consume.ssa_use
                && r.def_ssa == consume.ssa_def
        }) {
            return false;
        }
        [
            (consume.ssa_use, base.use_start, base.use_end),
            (consume.ssa_def, base.def_start, base.def_end),
        ]
        .into_iter()
        .all(|(ssa, start, end)| {
            let Some(ssa) = ssa else { return false };
            one(roster
                .versions
                .iter()
                .filter(|v| v.local == consume.local && v.ssa == ssa))
            .is_some_and(|v| v.variables.iter().copied().eq(start..end))
        })
    };
    let same_window =
        |boundary: &super::super::ownership_occurrence::Availability<Window>,
         consume: &super::super::ownership_occurrence::Consumption| {
            matches!((boundary,&consume.projected),(Present(Window::UseDef{use_start:a,use_end:b,def_start:c,def_end:d}),Present(w)) if (*a,*b,*c,*d)==(w.use_start,w.use_end,w.def_start,w.def_end))
        };
    if native.receiver != source.syntax.destination
        || actual.local != native.receiver.local
        || actual.projection != native.receiver.projection
        || actual.point != receiver.point
        || actual.ssa_def.is_none()
        || !roster_matches(actual)
        || !same_window(&receiver.actual, actual)
    {
        return Err(bad_receiver());
    }
    let bad_argument = || {
        hold(
            HoldReason::ArgumentCorrespondence,
            Some(argument.ordinal),
            None,
        )
    };
    let Expression::Call { operands } = &source.syntax.expression else {
        return Err(bad_argument());
    };
    if argument.argument_index != Some(native.argument_index)
        || native.argument_index.checked_add(1) != Some(candidate.parameter as usize)
    {
        return Err(bad_argument());
    }
    let Some(OperandSyntax::Copy { place } | OperandSyntax::Move { place }) =
        operands.get(native.argument_index)
    else {
        return Err(bad_argument());
    };
    if place != &native.argument {
        return Err(bad_argument());
    }
    let Present(registration_id) = argument.call_arg_registration else {
        return Err(bad_argument());
    };
    let registration = one(facts
        .call_arg_registrations
        .iter()
        .filter(|r| r.point.construction == call.construction && r.ordinal == registration_id))
    .ok_or_else(bad_argument)?;
    if registration.proxy_local != native.argument.local
        || !native.argument.projection.is_empty()
        || argument.actual != Present(registration.window.clone())
    {
        return Err(bad_argument());
    }
    let Present(argument_id) = argument.actual_occurrence else { return Err(bad_argument()) };
    let consumed = one(facts
        .consumes
        .iter()
        .filter(|c| c.point.construction == call.construction && c.ordinal == argument_id))
    .ok_or_else(bad_argument)?;
    if registration.source_occurrence != Present(argument_id)
        || registration.point != consumed.point
        || !same_window(&argument.actual, consumed)
        || consumed.ssa_use.is_none()
        || !roster_matches(consumed)
    {
        return Err(bad_argument());
    }
    // The independent registration validates the erased proxy's source, not
    // equality of the proxy local and its underlying SSA owner.
    let scoped = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_ref() == Some(&call.caller)
    };
    let boundaries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|r| scoped(&r.point))
        .cloned()
        .collect();
    let registrations: Vec<_> = facts
        .call_arg_registrations
        .iter()
        .filter(|r| scoped(&r.point))
        .cloned()
        .collect();
    let consumes: Vec<_> = facts
        .consumes
        .iter()
        .filter(|r| scoped(&r.point))
        .cloned()
        .collect();
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|r| scoped(&r.point))
        .cloned()
        .collect();
    ownership_boundary::validate_shapes(&call.caller, &boundaries, &registrations)
        .map_err(|_| bad_argument())?;
    ownership_boundary::validate_links(
        &call.caller,
        &boundaries,
        &registrations,
        &consumes,
        &equations,
    )
    .map_err(|_| bad_argument())?;
    if !traversal_call::discover_metadata(facts, aliases).contains(candidate) {
        return Err(simple(HoldReason::TraversalIncomplete));
    }
    let traversal = traversal_return::classify_metadata(facts, &call.callee, aliases)
        .filter(|p| p.parameter == candidate.parameter)
        .ok_or_else(|| simple(HoldReason::TraversalIncomplete))?;
    let return_key = format!("{}::_0@d0", call.callee);
    let target = one(native.callee_returns.iter().filter(|r| {
        r.target.root == return_key
            && r.target.depth == 0
            && r.target.root_dereferences == 0
            && r.target.field.is_none()
    }))
    .ok_or_else(|| simple(HoldReason::MissingReturnFlow))?;
    if target.unknown {
        return Err(simple(HoldReason::UnknownReturnOrigin));
    }
    let parameter_key = format!("{}::_{}@d0", call.callee, candidate.parameter);
    let mut fields = std::collections::BTreeSet::new();
    for id in &traversal.readers {
        let equation = one(facts
            .equations
            .iter()
            .filter(|e| e.point.construction == id.construction && e.ordinal == id.ordinal))
        .ok_or_else(|| simple(HoldReason::TraversalIncomplete))?;
        let reader = one(facts.reader_plan.candidates.iter().filter(|reader| {
            reader.function == call.callee
                && Some(reader.block) == equation.point.block
                && Some(reader.statement) == equation.point.statement
                && reader.origin_parameter == candidate.parameter
        }))
        .ok_or_else(|| simple(HoldReason::TraversalIncomplete))?;
        fields.insert(reader.field_key.as_str());
    }
    if target.incoming.is_empty()
        || target
            .incoming
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != target.incoming.len()
        || target.target.kind_slot != OriginAvailability::Present(return_key)
        || target.incoming.iter().any(|key| {
            key.root != parameter_key
                || key.depth != 0
                || match &key.field {
                    None => {
                        key.root_dereferences != 0
                            || key.kind_slot != OriginAvailability::Present(parameter_key.clone())
                    }
                    Some(field) => {
                        key.root_dereferences != 1
                            || !fields.contains(field.as_str())
                            || key.kind_slot != OriginAvailability::Present(field.clone())
                    }
                }
        })
    {
        return Err(simple(HoldReason::UnexpectedIncomingOrigin));
    }
    if !native.caller_value_flow {
        return Err(simple(HoldReason::CallerFlowAbsent));
    }
    Ok(Proof {
        candidate: candidate.clone(),
        traversal,
        native: native.clone(),
        argument_registration: registration_id,
        argument_consume: Some(argument_id),
        receiver_consume: receiver_id,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        super::{super::ownership_occurrence::Availability, graph_tests::with_facts},
        *,
    };

    const CODE: &str = r#"
pub struct Node {left:*mut Node}
pub unsafe fn minimum(mut node:*mut Node)->*mut Node {
    while !(*node).left.is_null() {node=(*node).left;}
    node
}
pub unsafe fn caller(first:*mut Node,second:*mut Node)->*mut Node {
    let left=minimum(first);
    let right=minimum(second);
    if right.is_null() {left} else {right}
}
"#;

    fn with_calls(check: impl FnOnce(&Facts, &[traversal_call::Candidate]) + Send) {
        with_facts(CODE, move |facts| {
            assert_eq!(facts.constructions, 1);
            let calls = traversal_call::discover(facts);
            assert_eq!(calls.len(), 2, "two independent call identities");
            assert_ne!(calls[0].call, calls[1].call);
            check(facts, &calls);
        });
    }

    fn native_mut<'a>(
        facts: &'a mut Facts,
        candidate: &traversal_call::Candidate,
    ) -> &'a mut traversal_native::CallObservation {
        facts
            .traversal_native
            .as_mut()
            .unwrap()
            .calls
            .iter_mut()
            .find(|row| row.call == candidate.call)
            .unwrap()
    }

    fn expect_hold(
        facts: &Facts,
        candidate: &traversal_call::Candidate,
        reason: HoldReason,
    ) -> Hold {
        let hold = match certify(facts, candidate) {
            Err(hold) => hold,
            Ok(proof) => panic!(
                "typed hold {reason:?} required at {:?}, got {proof:?}",
                candidate.call
            ),
        };
        assert_eq!(
            hold.reason, reason,
            "typed hold at {:?}: {hold:?}",
            candidate.call
        );
        assert_eq!(
            hold.call, candidate.call,
            "hold must identify the actual rejected call"
        );
        hold
    }

    #[test]
    fn c05_traversal_correspondence_two_exact_calls_join_native_and_ssa() {
        with_calls(|facts, calls| {
            for candidate in calls {
                let proof = certify(facts, candidate).expect("complete static correspondence");
                assert_eq!(&proof.candidate, candidate);
                assert_eq!(proof.native.call, candidate.call);
                assert_eq!(proof.traversal.function, candidate.call.callee);
                assert_eq!(proof.traversal.parameter, candidate.parameter);
                assert!(!proof.traversal.readers.is_empty());
                let argument = facts
                    .boundary_substitutions
                    .iter()
                    .find(|row| {
                        row.point.construction == candidate.call.construction
                            && row.ordinal == candidate.argument_boundary
                    })
                    .unwrap();
                let receiver = facts
                    .boundary_substitutions
                    .iter()
                    .find(|row| {
                        row.point.construction == candidate.call.construction
                            && row.ordinal == candidate.receiver_boundary
                    })
                    .unwrap();
                let Availability::Present(registration) = argument.call_arg_registration else {
                    panic!("actual proxy registration")
                };
                assert_eq!(proof.argument_registration, registration);
                assert_eq!(
                    proof.argument_consume,
                    match argument.actual_occurrence {
                        Availability::Present(id) => Some(id),
                        Availability::Missing(_) => None,
                    }
                );
                assert_eq!(
                    receiver.actual_occurrence,
                    Availability::Present(proof.receiver_consume)
                );
                assert_eq!(
                    proof.native.argument_index + 1,
                    candidate.parameter as usize
                );
            }
        });
    }

    #[test]
    fn c05_traversal_correspondence_absent_and_duplicate_native_calls_are_typed() {
        with_calls(|facts, calls| {
            let candidate = &calls[0];
            let mut missing = facts.clone();
            missing.traversal_native = None;
            expect_hold(&missing, candidate, HoldReason::NativeFlowsUnavailable);
            let mut missing = facts.clone();
            let inputs = missing.traversal_native.as_mut().unwrap();
            inputs.status = traversal_native::Status::NativeFlowsUnavailable;
            inputs.calls.clear();
            expect_hold(&missing, candidate, HoldReason::NativeFlowsUnavailable);
            let mut missing = facts.clone();
            missing
                .traversal_native
                .as_mut()
                .unwrap()
                .calls
                .retain(|row| row.call != candidate.call);
            expect_hold(&missing, candidate, HoldReason::MissingCallObservation);
            let mut duplicate = facts.clone();
            let copy = native_mut(&mut duplicate, candidate).clone();
            duplicate
                .traversal_native
                .as_mut()
                .unwrap()
                .calls
                .push(copy);
            expect_hold(&duplicate, candidate, HoldReason::AmbiguousCallObservation);
        });
    }

    #[test]
    fn c05_traversal_correspondence_swapped_actual_and_receiver_keep_call_identity() {
        with_calls(|facts, calls| {
            let other = facts
                .traversal_native
                .as_ref()
                .unwrap()
                .calls
                .iter()
                .find(|row| row.call == calls[1].call)
                .unwrap();
            let mut swapped = facts.clone();
            let original = native_mut(&mut swapped, &calls[0]);
            assert_ne!(original.argument, other.argument);
            original.argument = other.argument.clone();
            expect_hold(&swapped, &calls[0], HoldReason::ArgumentCorrespondence);
            let mut swapped = facts.clone();
            let original = native_mut(&mut swapped, &calls[0]);
            assert_ne!(original.receiver, other.receiver);
            original.receiver = other.receiver.clone();
            let hold = expect_hold(&swapped, &calls[0], HoldReason::ReceiverConsumeMismatch);
            assert_eq!(hold.boundary, Some(calls[0].receiver_boundary));
        });
    }

    #[test]
    fn c05_traversal_correspondence_unknown_or_unrelated_return_origin_is_typed() {
        with_calls(|facts, calls| {
            let candidate = &calls[0];
            let target = |row: &traversal_native::ReturnFlow| {
                row.target.depth == 0
                    && row.target.root_dereferences == 0
                    && row.target.field.is_none()
            };
            let mut unknown = facts.clone();
            native_mut(&mut unknown, candidate)
                .callee_returns
                .iter_mut()
                .find(|row| target(row))
                .unwrap()
                .unknown = true;
            expect_hold(&unknown, candidate, HoldReason::UnknownReturnOrigin);
            let mut unrelated = facts.clone();
            let returned = native_mut(&mut unrelated, candidate)
                .callee_returns
                .iter_mut()
                .find(|row| target(row))
                .unwrap();
            let mut foreign = returned.incoming.first().unwrap().clone();
            foreign.root = "unrelated::_1@d0".into();
            returned.incoming.push(foreign);
            expect_hold(&unrelated, candidate, HoldReason::UnexpectedIncomingOrigin);
            let mut missing = facts.clone();
            native_mut(&mut missing, candidate).callee_returns.clear();
            expect_hold(&missing, candidate, HoldReason::MissingReturnFlow);
            let mut absent = facts.clone();
            native_mut(&mut absent, candidate).caller_value_flow = false;
            expect_hold(&absent, candidate, HoldReason::CallerFlowAbsent);
        });
    }

    #[test]
    fn c05_traversal_correspondence_other_call_receiver_consume_is_typed() {
        with_calls(|facts, calls| {
            let other = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.construction == calls[1].call.construction
                        && row.ordinal == calls[1].receiver_boundary
                })
                .unwrap()
                .actual_occurrence
                .clone();
            let Availability::Present(other_id) = other else { panic!("other receiver consume") };
            let mut wrong = facts.clone();
            let receiver = wrong
                .boundary_substitutions
                .iter_mut()
                .find(|row| {
                    row.point.construction == calls[0].call.construction
                        && row.ordinal == calls[0].receiver_boundary
                })
                .unwrap();
            assert_ne!(receiver.actual_occurrence, Availability::Present(other_id));
            receiver.actual_occurrence = Availability::Present(other_id);
            let hold = expect_hold(&wrong, &calls[0], HoldReason::ReceiverConsumeMismatch);
            assert_eq!(hold.boundary, Some(calls[0].receiver_boundary));
            assert_eq!(hold.consume, Some(other_id));
        });
    }
    #[test]
    fn c05_traversal_correspondence_duplicate_incoming_origin_is_rejected() {
        with_calls(|facts, calls| {
            certify(facts, &calls[0]).unwrap();
            let mut duplicate = facts.clone();
            let flow = native_mut(&mut duplicate, &calls[0])
                .callee_returns
                .iter_mut()
                .find(|r| {
                    r.target.depth == 0
                        && r.target.root_dereferences == 0
                        && r.target.field.is_none()
                })
                .unwrap();
            flow.incoming.push(flow.incoming[0].clone());
            expect_hold(&duplicate, &calls[0], HoldReason::UnexpectedIncomingOrigin);
        });
    }
    #[test]
    fn c05_traversal_correspondence_stale_receiver_ssa_is_rejected() {
        with_calls(|facts, calls| {
            let proof = certify(facts, &calls[0]).unwrap();
            let mut stale = facts.clone();
            let consume = stale
                .consumes
                .iter_mut()
                .find(|c| {
                    c.ordinal == proof.receiver_consume
                        && c.point.construction == calls[0].call.construction
                })
                .unwrap();
            consume.ssa_def = Some(u32::MAX);
            let hold = expect_hold(&stale, &calls[0], HoldReason::ReceiverConsumeMismatch);
            assert_eq!(hold.consume, Some(proof.receiver_consume));
        });
    }
    #[test]
    fn c05_traversal_correspondence_discarded_reader_cannot_explain_return_origin() {
        let code=CODE.replace("pub struct Node {left:*mut Node}","pub struct Node {left:*mut Node,right:*mut Node}")
            .replace("while !(*node).left.is_null()", "let discarded=(*node).right;let _seen=discarded.is_null();while !(*node).left.is_null()");
        with_facts(&code, |facts| {
            let candidate = traversal_call::discover(facts).remove(0);
            certify(facts, &candidate).unwrap();
            assert!(
                facts
                    .reader_plan
                    .candidates
                    .iter()
                    .any(|r| r.function == "minimum" && r.field_key == "Node::field1@d0")
            );
            let mut wrong = facts.clone();
            let flow = native_mut(&mut wrong, &candidate)
                .callee_returns
                .iter_mut()
                .find(|r| {
                    r.target.depth == 0
                        && r.target.root_dereferences == 0
                        && r.target.field.is_none()
                })
                .unwrap();
            let mut unrelated = flow
                .incoming
                .iter()
                .find(|k| k.field.is_some())
                .unwrap()
                .clone();
            unrelated.field = Some("Node::field1@d0".into());
            unrelated.kind_slot = super::super::super::origin_evidence::OriginAvailability::Present(
                "Node::field1@d0".into(),
            );
            flow.incoming.push(unrelated);
            expect_hold(&wrong, &candidate, HoldReason::UnexpectedIncomingOrigin);
        });
    }
    #[test]
    fn c05_traversal_correspondence_snapshot_rebuilds_proofs_and_missing_inputs() {
        with_calls(|facts, _| {
            let snapshot = super::super::snapshot::Snapshot::capture(facts, 0).unwrap();
            assert_eq!(snapshot.traversal_correspondences.len(), 2);
            assert!(snapshot.traversal_correspondences.iter().all(Result::is_ok));
            snapshot.validate().unwrap();
            let decoded: super::super::snapshot::Snapshot =
                serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
            decoded.validate().unwrap();
            let mut missing = decoded.clone();
            missing.metadata.traversal_native = None;
            assert!(
                missing.validate().is_err(),
                "missing native input cannot retain its proved correspondence"
            );
            let mut missing = decoded.clone();
            missing.traversal_correspondences.clear();
            assert!(
                missing.validate().is_err(),
                "independent call roster requires correspondence disposition"
            );
            let mut wrong = decoded;
            let other = wrong.metadata.traversal_native.as_ref().unwrap().calls[1]
                .receiver
                .clone();
            wrong.metadata.traversal_native.as_mut().unwrap().calls[0].receiver = other;
            assert!(wrong.validate().is_err());
        });
    }
}
