//! Observations from the already-derived native origin flows. No borrow grant.

use serde::{Deserialize, Serialize};

use super::{
    super::{
        crate_slots::CrateSlots, origin_evidence::SignatureKey, origin_summary::OriginSummaries,
        ownership_access::PlaceSyntax,
    },
    matched::CallKey,
    readers,
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Status {
    NativeFlowsUnavailable,
    /// Capture ran; per-call missing rows may still be present.
    Observed,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReturnFlow {
    pub(crate) target: SignatureKey,
    /// All non-reflexive native value-flow sources; storage aliases are not substituted.
    pub(crate) incoming: Vec<SignatureKey>,
    pub(crate) unknown: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CallObservation {
    pub(crate) call: CallKey,
    pub(crate) argument_index: usize,
    pub(crate) argument: PlaceSyntax,
    pub(crate) receiver: PlaceSyntax,
    pub(crate) callee_returns: Vec<ReturnFlow>,
    /// Flow-insensitive corroboration, not proof of this call's lifetime origin.
    pub(crate) caller_value_flow: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Inputs {
    pub(crate) status: Status,
    pub(crate) calls: Vec<CallObservation>,
    pub(crate) missing: Vec<MissingCall>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MissingReason {
    CallerFlow,
    CalleeFlow,
    ArgumentPlace,
    ReceiverPlace,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MissingCall {
    pub(crate) call: CallKey,
    pub(crate) argument_index: usize,
    pub(crate) reason: MissingReason,
}

pub(crate) fn collect(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    reader_plan: &readers::Plan,
) -> Inputs {
    use std::collections::BTreeMap;

    use rustc_middle::mir::Local;

    use super::super::{
        origin_evidence::{self, SourceCallee},
        origin_summary::SignatureRoot,
        ownership_access::{Expression, OperandSyntax},
        slots::SlotOwner,
    };
    let Some(flows) = origins.try_native_flows() else {
        return Inputs {
            status: Status::NativeFlowsUnavailable,
            calls: vec![],
            missing: vec![],
        };
    };
    let definitions: BTreeMap<_, _> = program
        .functions
        .iter()
        .map(|&f| (program.tcx.def_path_str(f), f))
        .collect();
    let mut result = Inputs {
        status: Status::Observed,
        calls: vec![],
        missing: vec![],
    };
    for &caller in &program.functions {
        for row in origin_evidence::occurrences(program, slots, caller) {
            let Some(SourceCallee::Local(callee)) = &row.callee else { continue };
            let Some(function) = reader_plan.functions.iter().find(|f| &f.function == callee)
            else {
                continue;
            };
            let [parameter] = function.returned_parameters.as_slice() else { continue };
            if !reader_plan
                .candidates
                .iter()
                .any(|c| &c.function == callee && c.origin_parameter == *parameter)
            {
                continue;
            }
            let Some(argument_index) = parameter.checked_sub(1).map(|i| i as usize) else {
                continue;
            };
            let call = CallKey {
                construction: 0,
                caller: row.site.function.clone(),
                block: row.site.block,
                statement: row.site.statement,
                callee: callee.clone(),
            };
            let observation = (|| -> Result<CallObservation, MissingReason> {
                let Expression::Call { operands } = &row.syntax.expression else {
                    return Err(MissingReason::ArgumentPlace);
                };
                let argument = match operands.get(argument_index) {
                    Some(OperandSyntax::Copy { place } | OperandSyntax::Move { place })
                        if place.projection.is_empty() =>
                    {
                        place.clone()
                    }
                    _ => return Err(MissingReason::ArgumentPlace),
                };
                let receiver = row.syntax.destination.clone();
                if !receiver.projection.is_empty() {
                    return Err(MissingReason::ReceiverPlace);
                }
                let caller_flow = flows.get(&caller).ok_or(MissingReason::CallerFlow)?;
                let callee_id = *definitions.get(callee).ok_or(MissingReason::CalleeFlow)?;
                let native = &flows
                    .get(&callee_id)
                    .ok_or(MissingReason::CalleeFlow)?
                    .summary;
                let mut callee_returns = Vec::new();
                for (target, slot) in native
                    .slots
                    .iter_enumerated()
                    .filter(|(_, slot)| matches!(slot.place.root, SignatureRoot::Return))
                {
                    let mut incoming: Vec<_> = native
                        .slots
                        .iter_enumerated()
                        .filter(|(source, _)| {
                            *source != target && native.value_flows.contains(*source, target)
                        })
                        .map(|(_, source)| {
                            origin_evidence::signature_key(program, slots, callee_id, *source)
                        })
                        .collect();
                    incoming.sort();
                    incoming.dedup();
                    callee_returns.push(ReturnFlow {
                        target: origin_evidence::signature_key(program, slots, callee_id, *slot),
                        incoming,
                        unknown: native.unknown_targets.contains(target),
                    });
                }
                callee_returns.sort_by(|a, b| a.target.cmp(&b.target));
                let caller_value_flow = caller_flow.body.depth0_value_flows().contains(&(
                    SlotOwner::Local(Local::from_u32(argument.local)),
                    SlotOwner::Local(Local::from_u32(receiver.local)),
                ));
                Ok(CallObservation {
                    call: call.clone(),
                    argument_index,
                    argument,
                    receiver,
                    callee_returns,
                    caller_value_flow,
                })
            })();
            match observation {
                Ok(row) => result.calls.push(row),
                Err(reason) => result.missing.push(MissingCall {
                    call,
                    argument_index,
                    reason,
                }),
            }
        }
    }
    result.calls.sort_by(|a, b| a.call.cmp(&b.call));
    result.missing.sort_by(|a, b| a.call.cmp(&b.call));
    result
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use rustc_hir::{ItemKind, OwnerNode};

    use super::{
        super::super::{
            origin_evidence, origin_flow,
            origins::compute_origins,
            ownership_access::{Expression, OperandSyntax},
        },
        *,
    };

    const TWO_CALLS: &str = r#"
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

    fn with_native(
        code: &str,
        check: impl FnOnce(&RustProgram<'_>, &CrateSlots, &OriginSummaries, &readers::Plan) + Send,
    ) {
        ::utils::compilation::run_compiler_on_str(code, move |tcx| {
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
            let program = RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let plan = readers::Plan::build(&readers::Inputs::collect(&program, &slots));
            let derivations = origin_flow::ORIGIN_DERIVATION_COUNT.with(|count| count.get());
            check(&program, &slots, &origins, &plan);
            assert_eq!(
                origin_flow::ORIGIN_DERIVATION_COUNT.with(|count| count.get()),
                derivations,
                "native observation must consume the existing derivation, never recompute it"
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn c05_traversal_native_distinguishes_two_calls_and_existing_flow_receipts() {
        with_native(TWO_CALLS, |program, slots, origins, plan| {
            let inputs = collect(program, slots, origins, plan);
            assert_eq!(inputs.status, Status::Observed);
            assert_eq!(inputs.calls.len(), 2);
            assert_eq!(
                inputs
                    .calls
                    .iter()
                    .map(|row| row.call.clone())
                    .collect::<BTreeSet<_>>()
                    .len(),
                2,
                "same callee never merges distinct source call occurrences"
            );
            let caller = *program
                .functions
                .iter()
                .find(|&&did| program.tcx.def_path_str(did) == "caller")
                .unwrap();
            let occurrences = origin_evidence::occurrences(program, slots, caller);
            let expected: Vec<_> = occurrences
                .iter()
                .filter(|row| {
                    row.callee == Some(origin_evidence::SourceCallee::Local("minimum".into()))
                })
                .collect();
            assert_eq!(expected.len(), 2);
            for observation in &inputs.calls {
                let source: Vec<_> = expected
                    .iter()
                    .filter(|row| {
                        row.site.function == observation.call.caller
                            && row.site.block == observation.call.block
                            && row.site.statement == observation.call.statement
                    })
                    .collect();
                assert_eq!(source.len(), 1, "exact call source: {:?}", observation.call);
                let source = source[0];
                assert_eq!(observation.call.callee, "minimum");
                assert_eq!(observation.argument_index, 0);
                assert_eq!(observation.receiver, source.syntax.destination);
                let Expression::Call { operands } = &source.syntax.expression else {
                    panic!("source call syntax")
                };
                let (OperandSyntax::Copy { place } | OperandSyntax::Move { place }) =
                    &operands[observation.argument_index]
                else {
                    panic!("exact actual argument place")
                };
                assert_eq!(&observation.argument, place);
                assert!(
                    observation.caller_value_flow,
                    "existing native caller edge: {:?}",
                    observation.call
                );
                assert!(!observation.callee_returns.is_empty());
                let target = observation
                    .callee_returns
                    .iter()
                    .find(|row| {
                        row.target.root == "minimum::_0@d0"
                            && row.target.depth == 0
                            && row.target.root_dereferences == 0
                            && row.target.field.is_none()
                    })
                    .unwrap();
                assert!(!target.unknown);
                assert!(
                    target
                        .incoming
                        .iter()
                        .any(|key| key.root == "minimum::_1@d0"
                            && key.depth == 0
                            && key.root_dereferences == 0
                            && key.field.is_none()),
                    "zero-iteration parameter-to-return relation must remain visible"
                );
            }
        });
    }

    #[test]
    fn c05_traversal_native_missing_carried_flows_is_explicit_unavailable() {
        with_native(TWO_CALLS, |program, slots, origins, plan| {
            let summaries_only: OriginSummaries = origins
                .iter()
                .map(|(&did, summary)| (did, summary.clone()))
                .collect();
            assert!(summaries_only.try_native_flows().is_none());
            let inputs = collect(program, slots, &summaries_only, plan);
            assert_eq!(
                inputs.status,
                Status::NativeFlowsUnavailable,
                "missing carried flow is not an empty successful observation"
            );
            assert!(inputs.calls.is_empty());
        });
    }

    #[test]
    fn c05_traversal_native_identity_return_is_not_a_preliminary_traversal() {
        with_native(
            r#"
pub unsafe fn identity(p:*mut i32)->*mut i32 {p}
pub unsafe fn caller(p:*mut i32)->*mut i32 {identity(p)}
"#,
            |program, slots, origins, plan| {
                let inputs = collect(program, slots, origins, plan);
                assert_eq!(inputs.status, Status::Observed);
                assert!(
                    inputs.calls.is_empty(),
                    "ordinary identity return does not become a traversal observation"
                );
            },
        );
    }
    #[test]
    fn c05_traversal_native_normative_facts_and_snapshot_preserve_observations() {
        super::super::graph_tests::with_facts(TWO_CALLS, |facts| {
            let input = facts
                .traversal_native
                .as_ref()
                .expect("always produced without export");
            assert_eq!(input.status, Status::Observed);
            assert_eq!(input.calls.len(), 2);
            assert!(input.missing.is_empty());
            let snapshot = super::super::snapshot::Snapshot::capture(facts, 0).unwrap();
            assert_eq!(snapshot.metadata.traversal_native.as_ref(), Some(input));
            let decoded: super::super::snapshot::Snapshot =
                serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
            assert_eq!(
                decoded.metadata.facts().traversal_native.as_ref(),
                Some(input)
            );
            decoded.validate().unwrap();
        });
    }
    #[test]
    fn c05_traversal_native_unrepresented_call_argument_is_not_omitted() {
        let code = TWO_CALLS.replace("minimum(first)", "minimum(0 as *mut Node)");
        with_native(&code, |program, slots, origins, plan| {
            let input = collect(program, slots, origins, plan);
            assert_eq!(input.status, Status::Observed);
            // The cast may be an explicit local; in either lowering the exact
            // original call remains an observation or an explicit missing row.
            assert_eq!(input.calls.len() + input.missing.len(), 2);
            let calls: std::collections::BTreeSet<_> = input
                .calls
                .iter()
                .map(|c| &c.call)
                .chain(input.missing.iter().map(|c| &c.call))
                .collect();
            assert_eq!(calls.len(), 2);
        });
    }
}
