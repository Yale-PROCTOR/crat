//! Value-origin classes, separate from ownership responsibility and identity.
//! A class records alternatives; it never manufactures an allocation endpoint.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    super::{
        ownership_access::ImmediateOrigin,
        ownership_boundary::{Role, Variables},
        ownership_occurrence::Availability,
    },
    facts::{EquationId, Facts},
    matched::CallKey,
    transport::{CandidateGraph, Evidence, Node},
};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub(crate) enum OriginAtom {
    Fresh(EquationId),
    Input(Node),
    /// Substitution supplies value origins, but an argument-return relation
    /// alone does not prove whether the caller retained or transferred it.
    UnclassifiedInput {
        formal: Node,
        actual: Node,
    },
    /// R367-2: the callee returned this formal port and the call's substitution
    /// named no actual for it — the deeper components of an argument whose root
    /// alone was matched. Keeping the port is the difference between "the
    /// analysis could not classify this" and "this is the caller's own token,
    /// on a component the boundary did not pair". No `Fresh | Null` test accepts
    /// it; `fold_caller::returned_token` is the only reader that admits it.
    UnresolvedInput {
        formal: Node,
        actual: Node,
    },
    Borrow(Node),
    Null,
    Unknown(Node),
}

pub(crate) type OriginSet = BTreeSet<OriginAtom>;
type Scope = (u32, String);

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ValueOrigins {
    #[serde(with = "super::matched::ordered_pairs")]
    values: BTreeMap<Node, OriginSet>,
}

impl ValueOrigins {
    /// Report 048: the streamed form of `serde_json::to_writer(&to_value(self))`,
    /// byte for byte (see `matched::write_value_seq`).
    pub(crate) fn write_canonical(&self, w: &mut dyn std::io::Write) -> Result<(), String> {
        w.write_all(b"{\"values\":").map_err(|e| e.to_string())?;
        super::matched::write_value_seq(w, &self.values)?;
        w.write_all(b"}").map_err(|e| e.to_string())
    }
}

/// Compiler-authenticated raw-pointer heads. A native reference or a struct's
/// first payload component is not the pointer whose kind this key describes.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct RawHead {
    pub(crate) function: String,
    pub(crate) local: u32,
    pub(crate) slot_key: String,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct NoRefCarrier {
    pub(crate) slot_key: String,
    pub(crate) values: Vec<Node>,
}

#[derive(Default)]
struct Function {
    nodes: BTreeSet<Node>,
    edges: BTreeSet<(Node, Node)>,
    seeds: BTreeMap<Node, OriginSet>,
    inputs: BTreeSet<Node>,
    outputs: BTreeSet<Node>,
    call_outputs: BTreeSet<Node>,
}

#[derive(Default)]
struct Call {
    inputs: BTreeMap<Node, BTreeSet<Node>>,
    outputs: Vec<(Node, Node)>,
}

fn extend(
    values: &mut BTreeMap<Node, OriginSet>,
    node: Node,
    atoms: impl IntoIterator<Item = OriginAtom>,
) -> bool {
    let target = values.entry(node).or_default();
    let before = target.len();
    target.extend(atoms);
    before != target.len()
}

impl ValueOrigins {
    pub(crate) fn build(facts: &Facts) -> Self {
        let graph = CandidateGraph::build(facts);
        Self::build_graph(facts, &graph)
    }

    pub(crate) fn build_metadata(
        facts: &Facts,
        aliases: &BTreeMap<EquationId, EquationId>,
    ) -> Result<Self, String> {
        Ok(Self::build_graph(
            facts,
            &CandidateGraph::build_metadata(facts, aliases)?,
        ))
    }

    fn build_graph(facts: &Facts, graph: &CandidateGraph) -> Self {
        let equations: BTreeMap<_, _> = facts
            .equations
            .iter()
            .map(|row| {
                (
                    EquationId {
                        construction: row.point.construction,
                        ordinal: row.ordinal,
                    },
                    row,
                )
            })
            .collect();
        let boundaries: BTreeMap<_, _> = facts
            .boundary_substitutions
            .iter()
            .map(|row| ((row.point.construction, row.ordinal), row))
            .collect();
        let mut functions: BTreeMap<Scope, Function> = BTreeMap::new();
        for roster in &facts.body_rosters {
            let Some(name) = &roster.point.function else { continue };
            let function = functions
                .entry((roster.point.construction, name.clone()))
                .or_default();
            for version in &roster.versions {
                function
                    .nodes
                    .extend(version.variables.iter().map(|&var| Node {
                        construction: roster.point.construction,
                        var,
                    }));
            }
        }
        for edge in &graph.edges {
            let point = match edge.evidence {
                Evidence::Transfer(id) => {
                    let Some(row) = equations.get(&id) else { continue };
                    let Some(transfer) = &row.transfer else { continue };
                    if !matches!(transfer.source, Availability::Present(_))
                        || !matches!(transfer.destination, Availability::Present(_))
                    {
                        continue;
                    }
                    &row.point
                }
                Evidence::Phi(id)
                | Evidence::Frame { equation: id, .. }
                | Evidence::TraversalFrame(id)
                | Evidence::ReferenceEffect(id) => {
                    let Some(row) = equations.get(&id) else { continue };
                    &row.point
                }
                Evidence::Boundary {
                    construction,
                    ordinal,
                    ..
                } => {
                    let Some(row) = boundaries.get(&(construction, ordinal)) else { continue };
                    if matches!(row.role, Role::CallArgument | Role::ReturnReceiver)
                        && row.licensing_role
                            != super::super::ownership_boundary::LicensingRole::Borrowed
                    {
                        continue;
                    }
                    &row.point
                }
            };
            let Some(name) = &point.function else { continue };
            let function = functions
                .entry((point.construction, name.clone()))
                .or_default();
            function.nodes.extend([edge.from, edge.to]);
            // Origin alternatives are independent of T2 endpoint retraction.
            // Including both possible copy roles is conservative; a possible
            // borrowed view below prevents a no-borrow classification.
            function.edges.insert((edge.from, edge.to));
        }
        for source in &graph.sources {
            let row = equations[&source.equation];
            let Some(name) = &row.point.function else { continue };
            let function = functions
                .entry((row.point.construction, name.clone()))
                .or_default();
            function.nodes.insert(source.node);
            extend(
                &mut function.seeds,
                source.node,
                [OriginAtom::Fresh(source.equation)],
            );
        }
        for view in &graph.borrowed_views {
            let row = equations[&view.guard.binding];
            let Some(name) = &row.point.function else { continue };
            let function = functions
                .entry((row.point.construction, name.clone()))
                .or_default();
            function.nodes.insert(view.view);
            extend(
                &mut function.seeds,
                view.view,
                [OriginAtom::Borrow(view.owner_before)],
            );
        }
        for (name, occurrences) in &facts.source_occurrences {
            for occurrence in occurrences {
                let atom = match occurrence.syntax.immediate_origin {
                    ImmediateOrigin::Borrow => Some(true),
                    ImmediateOrigin::Null => Some(false),
                    _ => None,
                };
                let Some(borrowed) = atom else { continue };
                for consume in facts.consumes.iter().filter(|consume| {
                    consume.point.function.as_ref() == Some(name)
                        && consume.point.block == Some(occurrence.site.block)
                        && consume.point.statement == Some(occurrence.site.statement)
                        && consume.local == occurrence.syntax.destination.local
                        && consume.projection == occurrence.syntax.destination.projection
                }) {
                    let Availability::Present(window) = &consume.projected else { continue };
                    if window.def_start == window.def_end {
                        continue;
                    }
                    let node = Node {
                        construction: consume.point.construction,
                        var: window.def_start,
                    };
                    let function = functions
                        .entry((consume.point.construction, name.clone()))
                        .or_default();
                    function.nodes.insert(node);
                    extend(
                        &mut function.seeds,
                        node,
                        [if borrowed {
                            OriginAtom::Borrow(node)
                        } else {
                            OriginAtom::Null
                        }],
                    );
                }
            }
        }
        let mut calls: BTreeMap<CallKey, Call> = BTreeMap::new();
        for row in &facts.boundary_substitutions {
            let Some(name) = &row.point.function else { continue };
            let scope = (row.point.construction, name.clone());
            let node = |var| Node {
                construction: row.point.construction,
                var,
            };
            match row.role {
                Role::Entry | Role::ExitReturn | Role::ExitOutput => {
                    let function = functions.entry(scope).or_default();
                    for pair in &row.matched {
                        let Variables::Single { var } = pair.formal else { continue };
                        let port = node(var);
                        function.nodes.insert(port);
                        if row.role == Role::Entry {
                            function.inputs.insert(port);
                            extend(&mut function.seeds, port, [OriginAtom::Input(port)]);
                        } else {
                            function.outputs.insert(port);
                        }
                    }
                }
                Role::CallArgument | Role::ReturnReceiver => {
                    if row.licensing_role
                        == super::super::ownership_boundary::LicensingRole::Borrowed
                    {
                        continue;
                    }
                    if row.licensing_role
                        == super::super::ownership_boundary::LicensingRole::TraversalBorrow
                        && !graph.edges.iter().any(|edge| {
                            matches!(edge.evidence, Evidence::Boundary { construction, ordinal, .. }
                                if construction == row.point.construction && ordinal == row.ordinal)
                                && edge.guard.is_some_and(|guard| !guard.required)
                        })
                    {
                        continue;
                    }
                    let (Some(block), Some(statement), Some(callee)) =
                        (row.point.block, row.point.statement, row.callee.clone())
                    else {
                        continue;
                    };
                    if !functions.contains_key(&(row.point.construction, callee.clone()))
                        || !matches!(row.actual_occurrence, Availability::Present(_))
                        || !row.unmatched_actual_vars.is_empty()
                        || !row.unmatched_formal_vars.is_empty()
                    {
                        continue;
                    }
                    let key = CallKey {
                        construction: row.point.construction,
                        caller: name.clone(),
                        block,
                        statement,
                        callee,
                    };
                    let call = calls.entry(key).or_default();
                    let function = functions.entry(scope).or_default();
                    if row.licensing_role
                        == super::super::ownership_boundary::LicensingRole::OriginalCell
                    {
                        // MAY origins include both alternatives. Keep each exact
                        // actual input; never overwrite one with another or call
                        // either symbolic input an owning contract here.
                        // Cache reconstruction uses no ASTs; the graph's already
                        // checked boundary edges carry the same alternatives.
                        for edge in graph.edges.iter().filter(|edge| matches!(edge.evidence, Evidence::Boundary { construction, ordinal, .. } if construction == row.point.construction && ordinal == row.ordinal)) {
                            let input = row.matched.iter().any(|pair| matches!(pair.formal, Variables::UseDef {use_var, ..} if node(use_var) == edge.to));
                            if input { call.inputs.entry(edge.to).or_default().insert(edge.from); function.nodes.insert(edge.from); }
                            else { call.outputs.push((edge.from, edge.to)); function.call_outputs.insert(edge.to); function.nodes.insert(edge.to); }
                        }
                        continue;
                    }
                    // TraversalBorrow retains the authenticated legacy MAY
                    // substitution. Its true caller-local frame arrives through
                    // the graph; a held candidate creates no returned Borrow atom.
                    for pair in &row.matched {
                        match (&pair.formal, &pair.actual) {
                            (
                                Variables::UseDef {
                                    use_var: formal_use,
                                    def_var: formal_def,
                                },
                                Variables::UseDef {
                                    use_var: actual_use,
                                    def_var: actual_def,
                                },
                            ) => {
                                call.inputs
                                    .entry(node(*formal_use))
                                    .or_default()
                                    .insert(node(*actual_use));
                                call.outputs.push((node(*formal_def), node(*actual_def)));
                                function.call_outputs.insert(node(*actual_def));
                                function
                                    .nodes
                                    .extend([node(*actual_use), node(*actual_def)]);
                            }
                            (Variables::Single { var }, Variables::UseDef { def_var, .. })
                                if row.role == Role::ReturnReceiver =>
                            {
                                call.outputs.push((node(*var), node(*def_var)));
                                function.call_outputs.insert(node(*def_var));
                                function.nodes.insert(node(*def_var));
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        for ((construction, name), function) in &mut functions {
            // A surviving route cannot certify the absence of an omitted
            // alternative. Independent CFG/SSA coverage must close first;
            // keep the failure in summaries so callers inherit it as well.
            let incomplete = super::coverage::validate_returns(facts, *construction, name).is_err();
            let incoming: BTreeSet<_> = function.edges.iter().map(|(_, target)| *target).collect();
            for &node in &function.nodes {
                if incomplete
                    || (!incoming.contains(&node)
                        && !function.call_outputs.contains(&node)
                        && !function.seeds.contains_key(&node))
                {
                    extend(&mut function.seeds, node, [OriginAtom::Unknown(node)]);
                }
            }
        }
        let mut summaries: BTreeMap<(Scope, Node), OriginSet> = BTreeMap::new();
        loop {
            let mut result = BTreeMap::new();
            let mut unresolved: BTreeMap<Scope, BTreeSet<Node>> = BTreeMap::new();
            let mut changed_summary = false;
            for (scope, function) in &functions {
                let mut values = function.seeds.clone();
                loop {
                    let mut changed = false;
                    for &(source, target) in &function.edges {
                        let atoms = values.get(&source).cloned().unwrap_or_default();
                        changed |= extend(&mut values, target, atoms);
                    }
                    for (key, call) in calls
                        .iter()
                        .filter(|(key, _)| (key.construction, key.caller.clone()) == *scope)
                    {
                        let callee = (key.construction, key.callee.clone());
                        for &(formal, actual) in &call.outputs {
                            let mut instantiated = OriginSet::new();
                            if summaries
                                .get(&(callee.clone(), formal))
                                .is_none_or(|atoms| atoms.is_empty())
                            {
                                unresolved.entry(scope.clone()).or_default().insert(actual);
                            }
                            for atom in summaries
                                .get(&(callee.clone(), formal))
                                .into_iter()
                                .flatten()
                            {
                                match atom {
                                    OriginAtom::Input(input) => {
                                        if let Some(arguments) = call.inputs.get(input) {
                                            for argument in arguments {
                                                instantiated.insert(
                                                    OriginAtom::UnclassifiedInput {
                                                        formal: *input,
                                                        actual: *argument,
                                                    },
                                                );
                                                instantiated.extend(
                                                    values
                                                        .get(argument)
                                                        .into_iter()
                                                        .flatten()
                                                        .copied(),
                                                );
                                            }
                                        } else {
                                            instantiated.insert(OriginAtom::UnresolvedInput {
                                                formal: *input,
                                                actual,
                                            });
                                        }
                                    }
                                    other => {
                                        instantiated.insert(*other);
                                    }
                                }
                            }
                            changed |= extend(&mut values, actual, instantiated);
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                for &output in &function.outputs {
                    let atoms = values.get(&output).cloned().unwrap_or_default();
                    let target = summaries.entry((scope.clone(), output)).or_default();
                    let before = target.len();
                    target.extend(atoms);
                    changed_summary |= target.len() != before;
                }
                for &node in &function.nodes {
                    let atoms = values.remove(&node).unwrap_or_default();
                    if atoms.is_empty() {
                        unresolved.entry(scope.clone()).or_default().insert(node);
                    }
                    result
                        .entry(node)
                        .or_insert_with(BTreeSet::new)
                        .extend(atoms);
                }
            }
            if !changed_summary {
                // Pending summaries are bottom during the least fixpoint so
                // valid wrappers do not acquire spurious Unknown. At closure,
                // unresolved alternatives must enter the next propagation;
                // returning Unknown only from `at` would lose them at joins.
                let mut changed_unknown = false;
                for (scope, nodes) in unresolved {
                    let function = functions.get_mut(&scope).expect("recorded scope");
                    for node in nodes {
                        changed_unknown |=
                            extend(&mut function.seeds, node, [OriginAtom::Unknown(node)]);
                    }
                }
                if changed_unknown {
                    continue;
                }
                return Self { values: result };
            }
        }
    }

    pub(crate) fn at(&self, node: Node) -> OriginSet {
        self.values
            .get(&node)
            .cloned()
            .unwrap_or_else(|| BTreeSet::from([OriginAtom::Unknown(node)]))
    }

    pub(crate) fn fresh_without_borrow(&self, node: Node) -> bool {
        let atoms = self.at(node);
        atoms
            .iter()
            .any(|atom| matches!(atom, OriginAtom::Fresh(_)))
            && atoms
                .iter()
                .all(|atom| matches!(atom, OriginAtom::Fresh(_) | OriginAtom::Null))
    }

    pub(crate) fn no_ref_carriers(&self, facts: &Facts) -> Vec<NoRefCarrier> {
        let mut carriers: BTreeMap<String, BTreeSet<Node>> = BTreeMap::new();
        for head in &facts.raw_pointer_heads {
            for roster in facts
                .body_rosters
                .iter()
                .filter(|row| row.point.function.as_ref() == Some(&head.function))
            {
                let reachable: BTreeSet<_> = roster
                    .blocks
                    .iter()
                    .filter(|block| block.reachable)
                    .map(|block| block.block)
                    .collect();
                let used_versions: BTreeSet<_> = roster
                    .consumes
                    .iter()
                    .filter(|consume| {
                        consume.local == head.local && reachable.contains(&consume.block)
                    })
                    .flat_map(|consume| std::iter::once(consume.use_ssa).chain(consume.def_ssa))
                    .collect();
                for version in roster.versions.iter().filter(|version| {
                    version.local == head.local && used_versions.contains(&version.ssa)
                }) {
                    let Some(&var) = version.variables.first() else { continue };
                    let node = Node {
                        construction: roster.point.construction,
                        var,
                    };
                    if self.fresh_without_borrow(node) {
                        carriers
                            .entry(head.slot_key.clone())
                            .or_default()
                            .insert(node);
                    }
                }
            }
        }
        carriers
            .into_iter()
            .map(|(slot_key, values)| NoRefCarrier {
                slot_key,
                values: values.into_iter().collect(),
            })
            .collect()
    }
}
