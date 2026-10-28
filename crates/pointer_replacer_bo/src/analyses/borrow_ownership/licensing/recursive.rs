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
#[cfg(test)]
pub(crate) fn certify_invocations(
    facts: &Facts,
    construction: u32,
    function: &str,
) -> Availability<RecursiveCertificate> {
    let transport = MatchedTransport::build(facts);
    certify_with_transport(facts, construction, function, &transport)
}

/// The per-function form (378 (a)'s reference; the freeze uses [`certify_all`]).
#[cfg(test)]
pub(crate) fn certify_with_transport(
    facts: &Facts,
    construction: u32,
    function: &str,
    transport: &MatchedTransport,
) -> Availability<RecursiveCertificate> {
    let graph = CallGraph::build(facts, construction);
    if !graph.known.contains(function) {
        return Availability::Missing("function coverage roster unavailable".into());
    }
    let scc = graph.reach_scc(function);
    certify_scc(facts, construction, &graph, &scc, transport)
}

/// **Relay main/378 (a), R1324-1.** One construction's call graph: the functions with a roster,
/// and each reachable local call between two of them. Built once per construction, not once per
/// function: it does not depend on the function being certified.
pub(crate) struct CallGraph {
    known: std::collections::BTreeSet<String>,
    calls: std::collections::BTreeSet<CallKey>,
    forward: std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
    reverse: std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
}

impl CallGraph {
    pub(crate) fn build(facts: &Facts, construction: u32) -> Self {
        use std::collections::{BTreeMap, BTreeSet};

        use super::super::origin_evidence::SourceCallee;
        let known: BTreeSet<_> = facts
            .body_rosters
            .iter()
            .filter(|row| row.point.construction == construction)
            .filter_map(|row| row.point.function.clone())
            .collect();
        #[cfg(test)]
        super::freeze_counts::call_graph_built();
        let rosters: BTreeMap<&str, &super::coverage::BodyRoster> = facts
            .body_rosters
            .iter()
            .filter(|row| row.point.construction == construction)
            .rev()
            .filter_map(|row| row.point.function.as_deref().map(|name| (name, row)))
            .collect();
        let mut calls = BTreeSet::new();
        let mut forward: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut reverse: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (caller, occurrences) in &facts.source_occurrences {
            if !known.contains(caller) {
                continue;
            }
            // The first roster of the caller, as `body_rosters.iter().find(..)` took it.
            let Some(roster) = rosters.get(caller.as_str()) else {
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
        Self {
            known,
            calls,
            forward,
            reverse,
        }
    }

    /// The function's strongly connected component: what it reaches and what reaches it.
    #[cfg(test)]
    fn reach_scc(&self, function: &str) -> std::collections::BTreeSet<String> {
        use std::collections::{BTreeMap, BTreeSet, VecDeque};
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
        reach(&self.forward)
            .intersection(&reach(&self.reverse))
            .cloned()
            .collect()
    }

    /// Every known function's SCC at once (Kosaraju, iterative): the same sets as
    /// [`Self::reach_scc`], each computed once instead of two reaches per function.
    fn sccs(&self) -> std::collections::BTreeMap<String, usize> {
        use std::collections::{BTreeMap, BTreeSet};
        let empty = BTreeSet::new();
        let next = |graph: &BTreeMap<String, BTreeSet<String>>, node: &str| -> Vec<String> {
            graph.get(node).unwrap_or(&empty).iter().cloned().collect()
        };
        let mut order = Vec::new();
        let mut seen = BTreeSet::new();
        for root in &self.known {
            if !seen.insert(root.clone()) {
                continue;
            }
            let mut stack = vec![(root.clone(), next(&self.forward, root), 0usize)];
            while let Some((node, children, at)) = stack.last_mut() {
                if *at < children.len() {
                    let child = children[*at].clone();
                    *at += 1;
                    if seen.insert(child.clone()) {
                        let grandchildren = next(&self.forward, &child);
                        stack.push((child, grandchildren, 0));
                    }
                } else {
                    order.push(node.clone());
                    stack.pop();
                }
            }
        }
        let mut component = BTreeMap::new();
        for (id, root) in order.iter().rev().enumerate() {
            if component.contains_key(root) {
                continue;
            }
            let mut stack = vec![root.clone()];
            component.insert(root.clone(), id);
            while let Some(node) = stack.pop() {
                for parent in next(&self.reverse, &node) {
                    if !component.contains_key(&parent) {
                        component.insert(parent.clone(), id);
                        stack.push(parent);
                    }
                }
            }
        }
        component
    }

    /// Relay main/383 (R1333-1): the SCC DAG's shape for the `matched:callgraph` mark -- its
    /// longest path in SCC levels, the non-trivial SCCs (more than one function, or one calling
    /// itself), the largest SCC's size, and the functions.
    pub(crate) fn scc_depth(&self) -> (usize, usize, usize, usize) {
        use std::collections::{BTreeMap, BTreeSet};
        let component = self.sccs();
        let mut members: BTreeMap<usize, usize> = BTreeMap::new();
        for id in component.values() {
            *members.entry(*id).or_default() += 1;
        }
        let mut dag: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        let mut self_calls = BTreeSet::new();
        for (caller, callees) in &self.forward {
            let Some(&from) = component.get(caller) else { continue };
            for callee in callees {
                let Some(&to) = component.get(callee) else { continue };
                if from == to {
                    self_calls.insert(from);
                } else {
                    dag.entry(from).or_default().insert(to);
                }
            }
        }
        // The longest path down from each SCC, by an iterative post-order over the DAG.
        let mut depth: BTreeMap<usize, usize> = BTreeMap::new();
        for &start in members.keys() {
            let mut stack = vec![(start, false)];
            while let Some((node, expanded)) = stack.pop() {
                if depth.contains_key(&node) {
                    continue;
                }
                let below = dag.get(&node).into_iter().flatten();
                if expanded {
                    let longest = below.map(|next| depth[next]).max().unwrap_or(0);
                    depth.insert(node, longest + 1);
                } else {
                    stack.push((node, true));
                    stack.extend(
                        below
                            .filter(|next| !depth.contains_key(*next))
                            .map(|next| (*next, false)),
                    );
                }
            }
        }
        let nontrivial = members
            .iter()
            .filter(|(id, size)| **size > 1 || self_calls.contains(*id))
            .count();
        (
            depth.values().copied().max().unwrap_or(0),
            nontrivial,
            members.values().copied().max().unwrap_or(0),
            component.len(),
        )
    }
}

/// **Relay main/378 (a).** Every function's certificate for one construction, in `functions`'
/// order: the call graph and its SCCs once, one certificate per SCC, shared by its members.
pub(crate) fn certify_all<'f>(
    facts: &Facts,
    construction: u32,
    functions: impl Iterator<Item = &'f String>,
    transport: &MatchedTransport,
) -> Vec<(String, Availability<RecursiveCertificate>)> {
    use std::collections::{BTreeMap, BTreeSet};
    let graph = CallGraph::build(facts, construction);
    let component = graph.sccs();
    let mut members: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    for (function, id) in &component {
        members.entry(*id).or_default().insert(function.clone());
    }
    let mut certified: BTreeMap<usize, Availability<RecursiveCertificate>> = BTreeMap::new();
    functions
        .map(|function| {
            let certificate = match component.get(function) {
                Some(id) if graph.known.contains(function) => certified
                    .entry(*id)
                    .or_insert_with(|| {
                        certify_scc(facts, construction, &graph, &members[id], transport)
                    })
                    .clone(),
                _ => Availability::Missing("function coverage roster unavailable".into()),
            };
            (function.clone(), certificate)
        })
        .collect()
}

fn certify_scc(
    facts: &Facts,
    construction: u32,
    graph: &CallGraph,
    scc: &std::collections::BTreeSet<String>,
    transport: &MatchedTransport,
) -> Availability<RecursiveCertificate> {
    use std::collections::BTreeSet;
    let applications: Vec<_> = graph
        .calls
        .iter()
        .filter(|call| scc.contains(&call.caller) && scc.contains(&call.callee))
        .cloned()
        .collect();
    if applications.is_empty() {
        return Availability::Missing("no recursive application in this function's SCC".into());
    }
    for member in scc {
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
