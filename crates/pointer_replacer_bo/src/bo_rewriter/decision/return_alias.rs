//! MIR-only observation of whether a call's returned value is consumed.
//! This records no library contract, retention verdict, or model decision.

use rustc_hash::FxHashSet;
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, Place, RETURN_PLACE, Statement, StatementKind,
    TerminatorKind,
    visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReturnUseState {
    Unused,
    Used,
    Unknown,
}

impl ReturnUseState {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Unused => "unused",
            Self::Used => "used",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnDestination {
    pub(crate) local: Local,
    /// Owned MIR projection spelling, empty for a plain local destination.
    pub(crate) projection: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnUseSite {
    pub(crate) location: Location,
    pub(crate) reason: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnUseObservation {
    pub(crate) call: Location,
    pub(crate) destination: Option<ReturnDestination>,
    pub(crate) normal_target: Option<BasicBlock>,
    pub(crate) state: ReturnUseState,
    pub(crate) uses: Vec<ReturnUseSite>,
    pub(crate) definitions: Vec<ReturnUseSite>,
    pub(crate) unknowns: Vec<ReturnUseSite>,
}

fn site(location: Location, reason: &'static str) -> ReturnUseSite {
    ReturnUseSite { location, reason }
}

fn canonicalize(sites: &mut Vec<ReturnUseSite>) {
    sites.sort_by_key(|site| {
        (
            site.location.block.as_u32(),
            site.location.statement_index,
            site.reason,
        )
    });
    sites.dedup();
}

struct LocalUses {
    destination: Local,
    uses: Vec<ReturnUseSite>,
    definitions: Vec<ReturnUseSite>,
    unknowns: Vec<ReturnUseSite>,
}

impl<'tcx> Visitor<'tcx> for LocalUses {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        // FakeRead can otherwise appear as an Inspect use. It describes
        // borrow-checking bookkeeping, not consumption of a returned pointer.
        if !matches!(statement.kind, StatementKind::FakeRead(..)) {
            self.super_statement(statement, location);
        }
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if place.local == self.destination {
            let ignored = !context.is_use()
                || matches!(
                    context,
                    PlaceContext::NonMutatingUse(
                        NonMutatingUseContext::FakeBorrow | NonMutatingUseContext::PlaceMention
                    )
                );
            if !ignored {
                if place.projection.is_empty() && context.is_place_assignment() {
                    let reason = match context {
                        PlaceContext::MutatingUse(MutatingUseContext::Call) => "call-definition",
                        PlaceContext::MutatingUse(MutatingUseContext::AsmOutput) => {
                            "asm-definition"
                        }
                        _ => "assignment-definition",
                    };
                    self.definitions.push(site(location, reason));
                } else if matches!(
                    context,
                    PlaceContext::MutatingUse(
                        MutatingUseContext::Deinit
                            | MutatingUseContext::SetDiscriminant
                            | MutatingUseContext::Yield
                            | MutatingUseContext::Drop
                            | MutatingUseContext::Retag
                    )
                ) {
                    self.unknowns
                        .push(site(location, "unresolved-result-context"));
                } else {
                    let reason = if !place.projection.is_empty() {
                        if context.is_place_assignment() {
                            "write-through-result"
                        } else if context.is_mutating_use() {
                            "mutable-projection-of-result"
                        } else {
                            "read-or-borrow-through-result"
                        }
                    } else {
                        match context {
                            PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy) => {
                                "copy-result"
                            }
                            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                                "move-result"
                            }
                            context if context.is_borrow() || context.is_address_of() => {
                                "borrow-result-local"
                            }
                            _ => "inspect-result",
                        }
                    };
                    self.uses.push(site(location, reason));
                }
            }
        }
        self.super_place(place, context, location);
    }
}

pub(crate) fn observe(body: &Body<'_>, call: Location) -> ReturnUseObservation {
    let mut result = ReturnUseObservation {
        call,
        destination: None,
        normal_target: None,
        state: ReturnUseState::Unknown,
        uses: Vec::new(),
        definitions: Vec::new(),
        unknowns: Vec::new(),
    };
    let Some(block) = body
        .basic_blocks
        .iter_enumerated()
        .find_map(|(index, block)| (index == call.block).then_some(block))
    else {
        result.unknowns.push(site(call, "call-block-missing"));
        return result;
    };
    if call.statement_index != block.statements.len() {
        result.unknowns.push(site(call, "not-terminator-location"));
        return result;
    }
    let Some(terminator) = block.terminator.as_ref() else {
        result.unknowns.push(site(call, "missing-call-terminator"));
        return result;
    };
    let (destination, normal_target) = match &terminator.kind {
        TerminatorKind::Call {
            destination,
            target,
            ..
        } => (*destination, *target),
        TerminatorKind::TailCall { .. } => {
            result.state = ReturnUseState::Used;
            result.uses.push(site(call, "tail-return"));
            return result;
        }
        _ => {
            result.unknowns.push(site(call, "not-a-call"));
            return result;
        }
    };
    result.destination = Some(ReturnDestination {
        local: destination.local,
        projection: if destination.projection.is_empty() {
            String::new()
        } else {
            format!("{:?}", destination.projection)
        },
    });
    result.normal_target = normal_target;
    let Some(target) = normal_target else {
        result.unknowns.push(site(call, "no-normal-return-target"));
        return result;
    };
    if !body
        .basic_blocks
        .iter_enumerated()
        .any(|(index, _)| index == target)
    {
        result
            .unknowns
            .push(site(call, "normal-flow-target-missing"));
        return result;
    }
    if !destination.projection.is_empty() {
        result.state = ReturnUseState::Used;
        result.uses.push(site(call, "projected-output-destination"));
        return result;
    }

    let mut observed = LocalUses {
        destination: destination.local,
        uses: Vec::new(),
        definitions: Vec::new(),
        unknowns: Vec::new(),
    };
    observed.visit_body(body);
    canonicalize(&mut observed.definitions);
    result.definitions = observed.definitions;
    if result.definitions.len() != 1 || result.definitions[0].location != call {
        result
            .unknowns
            .push(site(call, "multiple-or-unresolved-destination-definitions"));
    }
    if destination.local.as_usize() > 0 && destination.local.as_usize() <= body.arg_count {
        result
            .unknowns
            .push(site(call, "destination-overwrites-parameter"));
    }

    let mut reachable = FxHashSet::default();
    let mut pending = vec![target];
    while let Some(next) = pending.pop() {
        if !reachable.insert(next) {
            continue;
        }
        if next == call.block {
            result
                .unknowns
                .push(site(call, "normal-flow-reenters-call"));
            continue;
        }
        let Some(block) = body
            .basic_blocks
            .iter_enumerated()
            .find_map(|(index, block)| (index == next).then_some(block))
        else {
            result
                .unknowns
                .push(site(call, "normal-flow-target-missing"));
            continue;
        };
        let Some(terminator) = block.terminator.as_ref() else {
            result.unknowns.push(site(
                Location {
                    block: next,
                    statement_index: block.statements.len(),
                },
                "normal-flow-terminator-missing",
            ));
            continue;
        };
        pending.extend(terminator.successors());
    }
    result.uses = observed
        .uses
        .into_iter()
        .filter(|event| reachable.contains(&event.location.block))
        .collect();
    result.unknowns.extend(
        observed
            .unknowns
            .into_iter()
            .filter(|event| reachable.contains(&event.location.block)),
    );
    if destination.local == RETURN_PLACE {
        result.uses.push(site(call, "return-place-destination"));
    }
    canonicalize(&mut result.uses);
    canonicalize(&mut result.unknowns);
    result.state = if !result.unknowns.is_empty() {
        ReturnUseState::Unknown
    } else if result.uses.is_empty() {
        ReturnUseState::Unused
    } else {
        ReturnUseState::Used
    };
    result
}
