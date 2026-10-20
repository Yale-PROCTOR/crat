//! Recursive invocation certificate vocabulary. These records are not grants.

use super::{
    super::ownership_occurrence::Availability,
    facts::{EquationId, Facts},
    matched::{CallKey, MatchedTransport},
    transport::Node,
};

/// A generative binder template: every execution introduces a fresh scope.
/// This is not an ID shared by executions of a static recursive callsite.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum InvocationBinding {
    FreshPerExecution,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct InvocationBinder {
    pub(crate) application: CallKey,
    pub(crate) binding: InvocationBinding,
}

/// References the actual formal/actual matcher pair, not a numeric Var identity.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct SubstitutionKey {
    pub(crate) construction: u32,
    pub(crate) boundary: usize,
    pub(crate) matched: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct RecursiveApplication {
    pub(crate) call: CallKey,
    pub(crate) invocation: Availability<InvocationBinder>,
    pub(crate) substitutions: Availability<Vec<SubstitutionKey>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct ReturnKey {
    pub(crate) construction: u32,
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) terminal: usize,
}

/// A real allocation endpoint, fresh on each execution of that source event
/// inside its invocation. The equation key is not a dynamic object identity.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct SourceAnchor {
    pub(crate) equation: EquationId,
    pub(crate) binding: InvocationBinding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum PendingRequirement {
    OriginCompleteness,
    OwnedInputContract,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ReturnAnchors {
    pub(crate) returned: ReturnKey,
    pub(crate) value: Node,
    pub(crate) anchors: Vec<SourceAnchor>,
    pub(crate) instances: Vec<super::matched::SourceInstance>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct RecursiveCertificate {
    pub(crate) applications: Vec<RecursiveApplication>,
    pub(crate) returns: Availability<Vec<ReturnKey>>,
    /// Convenience only for a single common anchor. Licensing must use the
    /// per-return component relation below, never an unrelated SCC allocation.
    pub(crate) source_anchor: Availability<SourceAnchor>,
    pub(crate) value_anchors: Vec<ReturnAnchors>,
    pub(crate) pending: Vec<PendingRequirement>,
}

/// A structural, conditional certificate. Every recursive call introduces a
/// generative invocation scope and retains its exact matcher substitutions.
/// Origin/OwnedInput obligations remain pending; this is never a grant.
pub(crate) fn certify_invocations(
    facts: &Facts,
    construction: u32,
    function: &str,
) -> Availability<RecursiveCertificate> {
    let transport = MatchedTransport::build(facts);
    certify_with_transport(facts, construction, function, &transport)
}

pub(crate) fn certify_with_transport(
    facts: &Facts,
    construction: u32,
    function: &str,
    transport: &MatchedTransport,
) -> Availability<RecursiveCertificate> {
    use std::collections::{BTreeMap, BTreeSet, VecDeque};

    use super::super::origin_evidence::SourceCallee;
    let known: BTreeSet<_> = facts
        .body_rosters
        .iter()
        .filter(|row| row.point.construction == construction)
        .filter_map(|row| row.point.function.clone())
        .collect();
    if !known.contains(function) {
        return Availability::Missing("function coverage roster unavailable".into());
    }
    let mut calls = BTreeSet::new();
    let mut forward: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut reverse: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (caller, occurrences) in &facts.source_occurrences {
        if !known.contains(caller) {
            continue;
        }
        let Some(roster) = facts.body_rosters.iter().find(|row| {
            row.point.construction == construction && row.point.function.as_ref() == Some(caller)
        }) else {
            continue;
        };
        for occurrence in occurrences {
            let Some(SourceCallee::Local(callee)) = &occurrence.callee else { continue };
            if !known.contains(callee)
                || !roster
                    .blocks
                    .iter()
                    .any(|block| block.reachable && block.block == occurrence.site.block)
            {
                continue;
            }
            let call = CallKey {
                construction,
                caller: caller.clone(),
                block: occurrence.site.block,
                statement: occurrence.site.statement,
                callee: callee.clone(),
            };
            forward
                .entry(caller.clone())
                .or_default()
                .insert(callee.clone());
            reverse
                .entry(callee.clone())
                .or_default()
                .insert(caller.clone());
            calls.insert(call);
        }
    }
    let reach = |graph: &BTreeMap<String, BTreeSet<String>>| {
        let mut seen = BTreeSet::new();
        let mut pending = VecDeque::from([function.to_owned()]);
        while let Some(node) = pending.pop_front() {
            if seen.insert(node.clone()) {
                pending.extend(graph.get(&node).into_iter().flatten().cloned());
            }
        }
        seen
    };
    let scc: BTreeSet<_> = reach(&forward)
        .intersection(&reach(&reverse))
        .cloned()
        .collect();
    let applications: Vec<_> = calls
        .into_iter()
        .filter(|call| scc.contains(&call.caller) && scc.contains(&call.callee))
        .collect();
    if applications.is_empty() {
        return Availability::Missing("no recursive application in this function's SCC".into());
    }
    for member in &scc {
        if let Err(errors) = super::coverage::validate_returns(facts, construction, member) {
            return Availability::Missing(format!(
                "incomplete return coverage for {member}: {errors:?}"
            ));
        }
    }
    let applications = applications
        .into_iter()
        .map(|call| {
            let rows: Vec<_> = facts
                .boundary_substitutions
                .iter()
                .filter(|row| {
                    row.point.construction == construction
                        && row.point.function.as_ref() == Some(&call.caller)
                        && row.point.block == Some(call.block)
                        && row.point.statement == Some(call.statement)
                        && row.callee.as_ref() == Some(&call.callee)
                })
                .collect();
            let incomplete = rows.is_empty()
                || rows.iter().any(|row| {
                    !row.unmatched_actual_vars.is_empty()
                        || !row.unmatched_formal_vars.is_empty()
                        || (!row.matched.is_empty()
                            && !matches!(row.actual_occurrence, Availability::Present(_)))
                });
            let substitutions = if incomplete {
                Availability::Missing("recursive matcher correspondence incomplete".into())
            } else {
                Availability::Present(
                    rows.into_iter()
                        .flat_map(|row| {
                            (0..row.matched.len()).map(move |matched| SubstitutionKey {
                                construction,
                                boundary: row.ordinal,
                                matched,
                            })
                        })
                        .collect(),
                )
            };
            RecursiveApplication {
                invocation: Availability::Present(InvocationBinder {
                    application: call.clone(),
                    binding: InvocationBinding::FreshPerExecution,
                }),
                call,
                substitutions,
            }
        })
        .collect();
    let mut returns = Vec::new();
    let mut value_anchors = Vec::new();
    let mut anchors = BTreeSet::new();
    for terminal in facts.terminals.iter().filter(|row| {
        row.point.construction == construction
            && row.role == "return-output"
            && row
                .point
                .function
                .as_ref()
                .is_some_and(|name| scc.contains(name))
    }) {
        let (Some(block), Some(statement), Some(function)) = (
            terminal.point.block,
            terminal.point.statement,
            terminal.point.function.clone(),
        ) else {
            return Availability::Missing("return coordinate unavailable".into());
        };
        let returned = ReturnKey {
            construction,
            function,
            block,
            statement,
            terminal: terminal.ordinal,
        };
        if let Availability::Present(values) = &terminal.values {
            for value in values {
                let node = Node {
                    construction,
                    var: value.var,
                };
                let instances = transport.sources_for(node);
                let sources: BTreeSet<_> = instances.iter().map(|source| source.endpoint).collect();
                // sources_for is rooted on this exact returned component and
                // keeps call substitutions. An allocation elsewhere is no anchor.
                let sources: Vec<_> = sources
                    .into_iter()
                    .filter(|id| {
                        facts.equations.iter().any(|row| {
                            row.point.construction == id.construction
                                && row.ordinal == id.ordinal
                                && row.operation == "source"
                                && row.endpoint.is_some()
                        })
                    })
                    .collect();
                anchors.extend(sources.iter().copied());
                value_anchors.push(ReturnAnchors {
                    returned: returned.clone(),
                    value: node,
                    instances: instances.into_iter().collect(),
                    anchors: sources
                        .into_iter()
                        .map(|equation| SourceAnchor {
                            equation,
                            binding: InvocationBinding::FreshPerExecution,
                        })
                        .collect(),
                });
            }
        }
        returns.push(returned);
    }
    let source_anchor = if anchors.len() == 1 {
        Availability::Present(SourceAnchor {
            equation: *anchors.first().unwrap(),
            binding: InvocationBinding::FreshPerExecution,
        })
    } else {
        Availability::Missing(
            if anchors.is_empty() {
                "no allocation anchor on a return route"
            } else {
                "multiple anchors: use each return component's explicit anchor set"
            }
            .into(),
        )
    };
    Availability::Present(RecursiveCertificate {
        applications,
        returns: Availability::Present(returns),
        source_anchor,
        value_anchors,
        pending: vec![
            PendingRequirement::OriginCompleteness,
            PendingRequirement::OwnedInputContract,
        ],
    })
}
