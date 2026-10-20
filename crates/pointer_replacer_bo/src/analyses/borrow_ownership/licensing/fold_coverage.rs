//! Exhaustive return/local coverage prerequisite for G-FOLD internal closure.
use super::facts::Facts;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Error {
    MissingTypes,
    MissingRoster,
    ReturnCoverage,
    LocalCoverage {
        block: u32,
        statement: usize,
    },
    MissingTerminal {
        block: u32,
        statement: usize,
        local: u32,
    },
    Version {
        block: u32,
        statement: usize,
        local: u32,
    },
    TerminalLaw,
}

pub(crate) fn validate(
    facts: &Facts,
    construction: u32,
    function: &str,
) -> Result<Vec<usize>, Error> {
    use std::collections::{BTreeMap, BTreeSet};

    use super::super::ownership_occurrence::{self, Availability};
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == construction && p.function.as_deref() == Some(function)
    };
    let types = facts.fold_types.as_ref().ok_or(Error::MissingTypes)?;
    let locals: BTreeSet<_> = types
        .places
        .iter()
        .filter(|p| p.function == function && p.place.projection.is_empty())
        .map(|p| p.place.local)
        .collect();
    if locals.is_empty() {
        return Err(Error::MissingTypes);
    }
    let rosters: Vec<_> = facts
        .body_rosters
        .iter()
        .filter(|r| scope(&r.point))
        .collect();
    let [roster] = rosters.as_slice() else { return Err(Error::MissingRoster) };
    super::coverage::validate_returns(facts, construction, function)
        .map_err(|_| Error::ReturnCoverage)?;
    let mut inventory = Vec::new();
    let terminals: Vec<_> = facts
        .terminals
        .iter()
        .filter(|t| scope(&t.point))
        .cloned()
        .collect();
    for block in roster.blocks.iter().filter(|b| b.reachable) {
        let Some(statement) = block.return_statement else { continue };
        let local_error = || Error::LocalCoverage {
            block: block.block,
            statement,
        };
        let selections: Vec<_> = facts
            .return_selections
            .iter()
            .filter(|s| {
                scope(&s.point)
                    && s.point.block == Some(block.block)
                    && s.point.statement == Some(statement)
            })
            .collect();
        let [selection] = selections.as_slice() else { return Err(local_error()) };
        let selected: BTreeMap<_, _> = selection.locals.iter().copied().collect();
        if selected.len() != selection.locals.len()
            || selected.keys().copied().collect::<BTreeSet<_>>() != locals
        {
            return Err(local_error());
        }
        let at_return: Vec<_> = terminals
            .iter()
            .filter(|t| t.point.block == Some(block.block) && t.point.statement == Some(statement))
            .collect();
        for (&local, &ssa) in &selected {
            let error = || Error::Version {
                block: block.block,
                statement,
                local,
            };
            let matching: Vec<_> = at_return.iter().filter(|t| t.local == local).collect();
            let [terminal] = matching.as_slice() else {
                return Err(Error::MissingTerminal {
                    block: block.block,
                    statement,
                    local,
                });
            };
            if terminal.ssa != ssa {
                return Err(error());
            }
            let role = if local == 0 {
                "return-output"
            } else if local as usize <= roster.argument_count {
                "parameter-output"
            } else {
                "local-final-zero"
            };
            if terminal.role != role {
                return Err(error());
            }
            match ssa {
                Some(ssa) => {
                    let versions: Vec<_> = roster
                        .versions
                        .iter()
                        .filter(|v| v.local == local && v.ssa == ssa)
                        .collect();
                    let [version] = versions.as_slice() else { return Err(error()) };
                    let Availability::Present(values) = &terminal.values else {
                        return Err(error());
                    };
                    if values.iter().map(|v| v.var).collect::<Vec<_>>() != version.variables
                        || values
                            .iter()
                            .any(|v| matches!(v.path, Availability::Missing(_)))
                    {
                        return Err(error());
                    }
                }
                None => {
                    if !matches!(&terminal.values, Availability::Missing(_)) {
                        return Err(error());
                    }
                }
            }
            inventory.push(terminal.ordinal);
        }
        if at_return.len() != selected.len() {
            return Err(local_error());
        }
    }
    inventory.sort_unstable();
    let mut recorded: Vec<_> = terminals.iter().map(|t| t.ordinal).collect();
    recorded.sort_unstable();
    if recorded != inventory {
        return Err(Error::ReturnCoverage);
    }
    let boundaries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|b| scope(&b.point))
        .cloned()
        .collect();
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|e| scope(&e.point))
        .cloned()
        .collect();
    ownership_occurrence::validate_terminal_links(&terminals, &boundaries, &equations)
        .map_err(|_| Error::TerminalLaw)?;
    Ok(inventory)
}
