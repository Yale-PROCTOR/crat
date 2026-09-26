//! Candidate endpoint transport. Connectivity is not an ownership grant or a
//! proof that the recorded guard and linear responsibility obligations hold.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{
    super::{
        ownership_boundary::{Role, Variables},
        ownership_evidence::Endpoint,
        ownership_occurrence::PathStep,
    },
    facts::{EquationId, Facts},
};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub(crate) struct Node {
    pub(crate) construction: u32,
    pub(crate) var: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Rule {
    Copy,
    Return,
    Param,
    Frame,
    Phi,
    ReferenceEffect,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Evidence {
    Transfer(EquationId),
    Boundary {
        construction: u32,
        ordinal: usize,
        matched: usize,
    },
    Frame {
        equation: EquationId,
        consume: usize,
    },
    Phi(EquationId),
    ReferenceEffect(EquationId),
    TraversalFrame(EquationId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Guard {
    pub(crate) binding: EquationId,
    pub(crate) required: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Edge {
    pub(crate) from: Node,
    pub(crate) to: Node,
    pub(crate) rule: Rule,
    pub(crate) evidence: Evidence,
    pub(crate) guard: Option<Guard>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct EndpointNode {
    pub(crate) node: Node,
    pub(crate) equation: EquationId,
    pub(crate) endpoint: Endpoint,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct BorrowView {
    pub(crate) owner_before: Node,
    pub(crate) owner_after: Node,
    pub(crate) view: Node,
    pub(crate) guard: Guard,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum ExitRole {
    Return,
    ProjectedParameter { local: u32 },
}

/// A possible owning-output obligation, never a deallocator endpoint.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ExitCandidate {
    pub(crate) node: Node,
    pub(crate) terminal_ordinal: usize,
    pub(crate) role: ExitRole,
    pub(crate) path: Vec<PathStep>,
    pub(crate) role_certification_pending: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CandidateGraph {
    pub(crate) sources: Vec<EndpointNode>,
    pub(crate) sinks: Vec<EndpointNode>,
    pub(crate) edges: Vec<Edge>,
    pub(crate) borrowed_views: Vec<BorrowView>,
    /// Syntactic outputs; owning eligibility still requires source and gate proof.
    pub(crate) exits: Vec<ExitCandidate>,
}

impl CandidateGraph {
    /// Reconstruction consumes predicate identity metadata only; no ASTs.
    pub(crate) fn build_metadata(
        facts: &Facts,
        guard_aliases: &BTreeMap<EquationId, EquationId>,
    ) -> Result<Self, String> {
        validate_guard_aliases(facts, guard_aliases)?;
        Ok(Self::build_with_keys(facts, guard_aliases))
    }

    /// Directed candidate identity transport from actual producer records.
    pub(crate) fn build(facts: &Facts) -> Self {
        Self::build_with_keys(facts, &super::matched::guard_aliases(&facts.guards))
    }

    fn build_with_keys(facts: &Facts, guards: &BTreeMap<EquationId, EquationId>) -> Self {
        let mut graph = Self::default();
        for equation in &facts.equations {
            let id = EquationId {
                construction: equation.point.construction,
                ordinal: equation.ordinal,
            };
            let node = |var| Node {
                construction: id.construction,
                var,
            };
            let guarded = guards.contains_key(&id);
            if let Some(endpoint) = &equation.endpoint {
                if equation.validate().is_err() || !guarded {
                    continue;
                }
                let endpoint = EndpointNode {
                    node: node(equation.variables[0]),
                    equation: id,
                    endpoint: endpoint.clone(),
                };
                match equation.operation.as_str() {
                    "source" => graph.sources.push(endpoint),
                    "sink" => graph.sinks.push(endpoint),
                    _ => {}
                }
            }
            // era-5c: a phi null-join (`left <= right`) still lets the token
            // flow right-to-left; the may-flow graph keeps the edge.
            if (equation.operation == "equal"
                || (equation.operation == "null-join" && equation.point.phase == "phi"))
                && equation.transfer.is_none()
                && equation.variables.len() == 2
            {
                let (left, right) = (equation.variables[0], equation.variables[1]);
                if equation.point.phase == "phi" {
                    graph.edges.push(Edge {
                        from: node(right),
                        to: node(left),
                        rule: Rule::Phi,
                        evidence: Evidence::Phi(id),
                        guard: None,
                    });
                } else {
                    use super::super::ownership_occurrence::Availability::Present;
                    // An `equal` over the (use, def) pair of one slot of a
                    // consume's base window is identity transport, whichever
                    // producer emitted it. Two producers do:
                    //
                    //  * a projection frame, at the consume's own point, for the
                    //    slots the consumed place does not name; and
                    //  * `InferMode::lend`, for EVERY slot of the place, when a
                    //    callee only reads the pointer (`is_null`, `offset`).
                    //
                    // A lend is attributed to the call terminator while its
                    // consume sits at the statement that fed the call, and it
                    // covers the projected window, so neither point equality nor
                    // a projected-window exclusion may gate the edge. The window
                    // arithmetic is already exact: variables are unique per
                    // (local, version, slot), so the pair names one consume.
                    // Blocks still have to agree, which keeps an unrelated
                    // same-shaped equate elsewhere in the body out.
                    let framed = facts.consumes.iter().find(|consume| {
                        if consume.point.construction != equation.point.construction
                            || consume.point.function != equation.point.function
                            || consume.point.block != equation.point.block
                        {
                            return false;
                        }
                        let Present(base) = &consume.base else {
                            return false;
                        };
                        left >= base.use_start
                            && left < base.use_end
                            && right >= base.def_start
                            && right < base.def_end
                            && left - base.use_start == right - base.def_start
                    });
                    if let Some(consume) = framed {
                        graph.edges.push(Edge {
                            from: node(left),
                            to: node(right),
                            rule: Rule::Frame,
                            evidence: Evidence::Frame {
                                equation: id,
                                consume: consume.ordinal,
                            },
                            guard: None,
                        });
                    }
                }
            }
            let Some(transfer) = &equation.transfer else {
                continue;
            };
            if equation.operation == "guarded-original-cell-frame" {
                // Only the false-arm cell frame exists here. This is neither
                // a borrowed-view split nor a true-arm ownership call edge.
                use super::super::ownership_occurrence::Availability::Present;
                if guarded
                    && equation.validate().is_ok()
                    && let Present(source) = &transfer.source
                {
                    graph.edges.push(Edge {
                        from: node(transfer.source_use),
                        to: node(transfer.source_def),
                        rule: Rule::Frame,
                        evidence: Evidence::Frame {
                            equation: id,
                            consume: source.consume,
                        },
                        guard: Some(Guard {
                            binding: id,
                            required: false,
                        }),
                    });
                }
                continue;
            }
            if equation.operation == "guarded-reference-field" {
                // This is a delegated payload, not a non-owning pointer copy.
                // Its complete return/effect proof is required before transport.
                continue;
            }
            let guard = if equation.operation.starts_with("guarded-") {
                if !guarded {
                    continue;
                }
                let borrowed = Guard {
                    binding: id,
                    required: true,
                };
                graph.borrowed_views.push(BorrowView {
                    owner_before: node(transfer.source_use),
                    owner_after: node(transfer.source_def),
                    view: node(transfer.destination_def),
                    guard: borrowed,
                });
                graph.edges.push(Edge {
                    from: node(transfer.source_use),
                    to: node(transfer.source_def),
                    rule: Rule::Frame,
                    evidence: Evidence::Transfer(id),
                    guard: Some(borrowed),
                });
                Some(Guard {
                    binding: id,
                    required: false,
                })
            } else {
                None
            };
            let transport = match equation.operation.as_str() {
                "linear" => !transfer.by_move,
                "equal" => transfer.by_move,
                "guarded-copy" | "guarded-move" | "guarded-reader-copy" | "guarded-reader-move" => {
                    true
                }
                _ => false,
            };
            if !transport {
                continue;
            }
            graph.edges.push(Edge {
                from: node(transfer.source_use),
                to: node(transfer.destination_def),
                rule: Rule::Copy,
                evidence: Evidence::Transfer(id),
                guard,
            });
            if !transfer.by_move {
                graph.edges.push(Edge {
                    from: node(transfer.source_use),
                    to: node(transfer.source_def),
                    rule: Rule::Copy,
                    evidence: Evidence::Transfer(id),
                    guard,
                });
            }
        }
        for candidate in super::ref_effects::Plan::build(facts).candidates {
            let boundary = facts.boundary_substitutions.iter().find(|row| {
                row.point.construction == candidate.construction
                    && row.ordinal == candidate.boundary
            });
            let Some(boundary) = boundary else { continue };
            let Some(peel) = &boundary.reference_peel else { continue };
            let Variables::UseDef {
                use_var: outer_before,
                def_var: outer_after,
            } = peel.skipped
            else {
                continue;
            };
            let expected = [
                (
                    "guarded-reference-field",
                    &candidate.formation,
                    vec![
                        candidate.payload_before.var,
                        candidate.cell_after.var,
                        candidate.cell_before.var,
                    ],
                ),
                (
                    "guarded-reference-scalar-read",
                    &candidate.scalar_read,
                    vec![candidate.scalar_after.var, candidate.scalar_before.var],
                ),
                (
                    "guarded-reference-output",
                    &boundary.point,
                    vec![candidate.cell_after.var, candidate.payload_after.var],
                ),
                (
                    "guarded-reference-outer",
                    &boundary.point,
                    vec![outer_after, outer_before],
                ),
                (
                    "guarded-reference-view-zero",
                    &candidate.scalar_read,
                    vec![candidate.scalar_view_new.var, candidate.scalar_view_old.var],
                ),
            ];
            let mut ids = Vec::new();
            let mut predicates = BTreeSet::new();
            for (operation, point, variables) in expected {
                let rows: Vec<_> = facts
                    .equations
                    .iter()
                    .filter(|row| {
                        row.operation == operation
                            && &row.point == point
                            && row.variables == variables
                            && row.validate().is_ok()
                    })
                    .collect();
                let [row] = rows.as_slice() else { break };
                let id = EquationId {
                    construction: row.point.construction,
                    ordinal: row.ordinal,
                };
                let Some(&predicate) = guards.get(&id) else { break };
                ids.push(id);
                predicates.insert(predicate);
            }
            if ids.len() != 5 || predicates.len() != 1 {
                continue;
            }
            let binding = *predicates.first().unwrap();
            for (from, to, evidence, required) in [
                (
                    candidate.cell_before,
                    candidate.payload_before,
                    ids[0],
                    true,
                ),
                (
                    candidate.scalar_before,
                    candidate.scalar_after,
                    ids[1],
                    true,
                ),
                (candidate.payload_after, candidate.cell_after, ids[2], true),
                (candidate.cell_before, candidate.cell_after, ids[0], false),
            ] {
                graph.edges.push(Edge {
                    from,
                    to,
                    rule: Rule::ReferenceEffect,
                    evidence: Evidence::ReferenceEffect(evidence),
                    guard: Some(Guard { binding, required }),
                });
            }
        }
        for boundary in &facts.boundary_substitutions {
            if boundary.licensing_role
                == super::super::ownership_boundary::LicensingRole::OriginalCell
            {
                if let Some(arm) = super::cell_effects::call_arm(facts, boundary, guards) {
                    for (actual, required) in [(arm.original, true), (arm.legacy, false)] {
                        for (from, to) in [(actual.0, arm.formal.0), (arm.formal.1, actual.1)] {
                            graph.edges.push(Edge {
                                from: Node {
                                    construction: arm.candidate.call.construction,
                                    var: from,
                                },
                                to: Node {
                                    construction: arm.candidate.call.construction,
                                    var: to,
                                },
                                rule: Rule::Param,
                                evidence: Evidence::Boundary {
                                    construction: arm.candidate.call.construction,
                                    ordinal: boundary.ordinal,
                                    matched: 0,
                                },
                                guard: Some(Guard {
                                    binding: arm.guard,
                                    required,
                                }),
                            });
                        }
                    }
                }
                continue;
            }
            let boundary_guard = if boundary.licensing_role
                == super::super::ownership_boundary::LicensingRole::TraversalBorrow
            {
                let Some(binding) = super::traversal_call::guard_for(facts, boundary, guards)
                else {
                    continue;
                };
                // True-arm transport stays entirely in the caller. Full-window
                // frames are explicit equations, including components omitted
                // by a boundary matcher; formal ownership uses only the false arm.
                if boundary.role == Role::CallArgument {
                    for row in facts.equations.iter().filter(|row| {
                        row.point == boundary.point
                            && row.operation == "guarded-traversal-frame"
                            && row.validate().is_ok()
                    }) {
                        let id = EquationId {
                            construction: row.point.construction,
                            ordinal: row.ordinal,
                        };
                        if guards.get(&id) != Some(&binding) {
                            continue;
                        }
                        graph.edges.push(Edge {
                            from: Node {
                                construction: id.construction,
                                var: row.variables[0],
                            },
                            to: Node {
                                construction: id.construction,
                                var: row.variables[1],
                            },
                            rule: Rule::Frame,
                            evidence: Evidence::TraversalFrame(id),
                            guard: Some(Guard {
                                binding,
                                required: true,
                            }),
                        });
                    }
                }
                Some(Guard {
                    binding,
                    required: false,
                })
            } else {
                None
            };
            for (index, pair) in boundary.matched.iter().enumerate() {
                let construction = boundary.point.construction;
                let mut edge = |from, to, rule| {
                    graph.edges.push(Edge {
                        from: Node {
                            construction,
                            var: from,
                        },
                        to: Node {
                            construction,
                            var: to,
                        },
                        rule,
                        evidence: Evidence::Boundary {
                            construction,
                            ordinal: boundary.ordinal,
                            matched: index,
                        },
                        guard: boundary_guard,
                    })
                };
                match (boundary.role, &pair.actual, &pair.formal) {
                    (
                        Role::ReturnReceiver,
                        Variables::UseDef { def_var, .. },
                        Variables::Single { var },
                    ) => edge(*var, *def_var, Rule::Return),
                    (
                        Role::ExitReturn,
                        Variables::Single { var: actual },
                        Variables::Single { var: formal },
                    ) => edge(*actual, *formal, Rule::Return),
                    (
                        Role::Entry,
                        Variables::Single { var: actual },
                        Variables::Single { var: formal },
                    ) => edge(*formal, *actual, Rule::Param),
                    (
                        Role::CallArgument,
                        Variables::UseDef {
                            use_var: actual_use,
                            def_var: actual_def,
                        },
                        Variables::UseDef {
                            use_var: formal_use,
                            def_var: formal_def,
                        },
                    ) => {
                        if boundary.licensing_role
                            == super::super::ownership_boundary::LicensingRole::Borrowed
                        {
                            edge(*actual_use, *actual_def, Rule::Frame);
                        } else {
                            edge(*actual_use, *formal_use, Rule::Param);
                            edge(*formal_def, *actual_def, Rule::Param);
                        }
                    }
                    (
                        Role::ExitOutput,
                        Variables::Single { var: actual },
                        Variables::Single { var: formal },
                    ) => edge(*actual, *formal, Rule::Param),
                    _ => {}
                }
            }
        }
        use super::super::ownership_occurrence::Availability::Present;
        for terminal in &facts.terminals {
            let Present(values) = &terminal.values else { continue };
            for value in values {
                let Present(path) = &value.path else { continue };
                if path.contains(&PathStep::ArrayElement) {
                    continue;
                }
                let (role, role_certification_pending) = match terminal.role.as_str() {
                    "return-output" if terminal.local == 0 => (ExitRole::Return, false),
                    // A by-value parameter's own field is local storage. An
                    // output must traverse a pointer to caller-visible storage;
                    // its writable/owning role still needs C's certification.
                    "parameter-output"
                        if terminal.local != 0 && path.contains(&PathStep::Deref) =>
                    {
                        (
                            ExitRole::ProjectedParameter {
                                local: terminal.local,
                            },
                            true,
                        )
                    }
                    _ => continue,
                };
                graph.exits.push(ExitCandidate {
                    node: Node {
                        construction: terminal.point.construction,
                        var: value.var,
                    },
                    terminal_ordinal: terminal.ordinal,
                    role,
                    path: path.clone(),
                    role_certification_pending,
                });
            }
        }
        graph
    }

    pub(crate) fn has_edge(&self, from: Node, to: Node, rule: Rule) -> bool {
        self.edges
            .iter()
            .any(|edge| edge.from == from && edge.to == to && edge.rule == rule)
    }

    pub(crate) fn forward(&self) -> BTreeSet<Node> {
        self.closure(self.sources.iter().map(|endpoint| endpoint.node), false)
    }

    pub(crate) fn backward(&self) -> BTreeSet<Node> {
        self.closure(self.sinks.iter().map(|endpoint| endpoint.node), true)
    }

    /// Candidate output demand is separate from free sinks. Reachability does
    /// not certify output roles or discharge any owning/guard obligation.
    pub(crate) fn backward_outputs(&self) -> BTreeSet<Node> {
        self.closure(self.exits.iter().map(|exit| exit.node), true)
    }

    /// Unknown predicates admit no route. The original candidate graph and
    /// endpoint identities are retained for retraction/restoration.
    pub(crate) fn forward_selected(
        &self,
        value: impl Fn(EquationId) -> Option<bool>,
    ) -> BTreeSet<Node> {
        let mut active = self.clone();
        active
            .sources
            .retain(|source| value(source.equation) == Some(true));
        active.edges.retain(|edge| {
            edge.guard
                .is_none_or(|guard| value(guard.binding) == Some(guard.required))
        });
        active.forward()
    }

    fn closure(&self, roots: impl Iterator<Item = Node>, reverse: bool) -> BTreeSet<Node> {
        let mut adjacency = BTreeMap::<Node, Vec<Node>>::new();
        for edge in &self.edges {
            let (from, to) = if reverse {
                (edge.to, edge.from)
            } else {
                (edge.from, edge.to)
            };
            adjacency.entry(from).or_default().push(to);
        }
        let mut seen = BTreeSet::new();
        let mut pending: VecDeque<_> = roots.collect();
        while let Some(node) = pending.pop_front() {
            if seen.insert(node) {
                pending.extend(adjacency.get(&node).into_iter().flatten().copied());
            }
        }
        seen
    }
}

/// Validate references and canonical classes without interpreting diagnostic
/// predicate text or creating solver objects. Missing required guards are held
/// by the candidate builder; dangling or noncanonical supplied keys are invalid.
pub(crate) fn validate_guard_aliases(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<(), String> {
    let guarded: BTreeSet<_> = facts
        .equations
        .iter()
        .filter(|row| row.guard.is_some() || matches!(row.operation.as_str(), "source" | "sink"))
        .map(|row| EquationId {
            construction: row.point.construction,
            ordinal: row.ordinal,
        })
        .collect();
    for (key, canonical) in aliases {
        if !guarded.contains(key)
            || !guarded.contains(canonical)
            || key.construction != canonical.construction
            || aliases.get(canonical) != Some(canonical)
        {
            return Err("invalid guard identity metadata".into());
        }
    }
    Ok(())
}
