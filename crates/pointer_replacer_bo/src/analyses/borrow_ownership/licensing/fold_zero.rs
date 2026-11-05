//! Pre-free descendant zeros derived from the exact child take, never sink zeros.
use std::collections::BTreeMap;

use super::{
    super::{
        ownership_access::{Expression, OperandSyntax},
        ownership_occurrence::{Availability::Present, PathStep},
    },
    facts::{EquationId, Facts},
    fold_internal::{Action, Error, Proof},
    transport::Node,
};

pub(crate) fn certify(
    facts: &Facts,
    proof: &Proof,
    order: &BTreeMap<u32, usize>,
    null_fields: &BTreeMap<Option<u32>, (usize, usize)>,
) -> Result<Vec<Action>, Error> {
    let takes: Vec<_> = proof.actions.iter().filter(|a| a.kind == "take").collect();
    if takes.is_empty() {
        return Ok(vec![]);
    }
    let position = |block: u32, statement: usize| {
        order
            .get(&block)
            .copied()
            .map(|block| (block, statement))
            .ok_or(Error::Coverage(line!()))
    };
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == proof.construction && p.function.as_deref() == Some(&proof.function)
    };
    let equations: BTreeMap<_, _> = facts
        .equations
        .iter()
        .filter(|e| scope(&e.point))
        .map(|e| {
            (
                EquationId {
                    construction: proof.construction,
                    ordinal: e.ordinal,
                },
                e,
            )
        })
        .collect();
    let free = proof
        .actions
        .iter()
        .find(|a| a.kind == "free")
        .ok_or(Error::Coverage(line!()))?;
    let free_position = position(free.block, free.statement)?;
    // Exact root narrowing casts and the original free's actual proxy must
    // have empty represented descendants before the root leaves that window.
    let occurrences = facts
        .source_occurrences
        .get(&proof.function)
        .ok_or(Error::Coverage(line!()))?;
    let mut targets = Vec::new();
    for occurrence in occurrences {
        // The path's own occurrences, as `certify_path` already does. Without
        // this a two-path body drags in the other path's sites and `position`
        // refuses them for having no place in this `order`.
        if !order.contains_key(&occurrence.site.block) {
            continue;
        }
        let source = match &occurrence.syntax.expression {
            Expression::Cast {
                operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
                cast,
                ..
            } if cast == "PtrToPtr" => Some(place),
            _ => None,
        };
        if let Some(source) = source {
            for consume in facts.consumes.iter().filter(|c| {
                scope(&c.point)
                    && c.point.block == Some(occurrence.site.block)
                    && c.point.statement == Some(occurrence.site.statement)
                    && c.local == source.local
                    && c.projection == source.projection
            }) {
                targets.push(consume);
            }
        }
        if occurrence.site.block == free.block && occurrence.site.statement == free.statement {
            let Expression::Call { operands } = &occurrence.syntax.expression else {
                return Err(Error::Coverage(line!()));
            };
            let [OperandSyntax::Copy { place } | OperandSyntax::Move { place }] =
                operands.as_slice()
            else {
                return Err(Error::Coverage(line!()));
            };
            let registrations: Vec<_> = facts
                .call_arg_registrations
                .iter()
                .filter(|r| scope(&r.point) && r.proxy_local == place.local && !r.by_reference)
                .collect();
            let [registration] = registrations.as_slice() else {
                return Err(Error::Coverage(line!()));
            };
            let Present(id) = registration.source_occurrence else {
                return Err(Error::Coverage(line!()));
            };
            let consume = facts
                .consumes
                .iter()
                .find(|c| scope(&c.point) && c.ordinal == id && c.point == registration.point)
                .ok_or(Error::Coverage(line!()))?;
            targets.push(consume);
        }
    }
    let mut result = Vec::new();
    for consume in targets {
        let (Present(window), Present(base), Present(paths)) =
            (&consume.projected, &consume.base, &consume.pointer_paths)
        else {
            return Err(Error::Coverage(line!()));
        };
        let block = consume.point.block.ok_or(Error::Coverage(line!()))?;
        let statement = consume.point.statement.ok_or(Error::Coverage(line!()))?;
        let target_position = position(block, statement)?;
        if target_position > free_position {
            continue;
        }
        for var in window.use_start + 1..window.use_end {
            let path = paths
                .get((var - base.use_start) as usize)
                .ok_or(Error::Coverage(line!()))?;
            if path.is_empty() {
                return Err(Error::Coverage(line!()));
            }
            let target = Node {
                construction: proof.construction,
                var,
            };
            // A component this path proved null before the root reaches the
            // free carries no token, so it owes no derived zero. The fact is
            // the certificate here, which is why the action carries no chain.
            if let Some(PathStep::Field { index, .. }) = path.get(1)
                && null_fields
                    .get(&Some(*index))
                    .is_some_and(|at| *at < target_position)
            {
                let action = Action {
                    block,
                    statement,
                    kind: "path-null-child-zero".into(),
                    equations: vec![],
                    zero_requirements: vec![target],
                };
                if !result.contains(&action) {
                    result.push(action);
                }
                continue;
            }
            let mut zeros: BTreeMap<Node, Vec<EquationId>> = BTreeMap::new();
            for take in &takes {
                if position(take.block, take.statement)? < target_position {
                    for &node in &take.zero_requirements {
                        zeros.insert(node, take.equations.clone());
                    }
                }
            }
            let mut laws = Vec::new();
            for action in &proof.actions {
                if !matches!(action.kind.as_str(), "component-law" | "projection-frame")
                    || position(action.block, action.statement)? >= target_position
                {
                    continue;
                }
                for id in &action.equations {
                    let e = equations.get(id).ok_or(Error::Coverage(line!()))?;
                    laws.push((*id, *e));
                }
            }
            loop {
                let before = zeros.len();
                for &(id, e) in &laws {
                    let (source, destinations) = if let Some(t) = &e.transfer {
                        match e.operation.as_str() {
                            "linear" | "equal" => {
                                (t.source_use, vec![t.destination_def, t.source_def])
                            }
                            _ => continue,
                        }
                    } else if e.operation == "equal" && e.variables.len() == 2 {
                        (e.variables[0], vec![e.variables[1]])
                    } else {
                        continue;
                    };
                    let Some(chain) = zeros
                        .get(&Node {
                            construction: proof.construction,
                            var: source,
                        })
                        .cloned()
                    else {
                        continue;
                    };
                    for var in destinations {
                        let mut chain = chain.clone();
                        chain.push(id);
                        zeros
                            .entry(Node {
                                construction: proof.construction,
                                var,
                            })
                            .or_insert(chain);
                    }
                }
                if zeros.len() == before {
                    break;
                }
            }
            let equations = zeros.remove(&target).ok_or(Error::UnaccountedToken)?;
            let action = Action {
                block,
                statement,
                kind: "pre-free-child-zero".into(),
                equations,
                zero_requirements: vec![target],
            };
            if !result.contains(&action) {
                result.push(action);
            }
        }
    }
    Ok(result)
}
