//! Conditional internal responsibility certificates for G-FOLD.
//! These straight-line records are not caller grants or selected field schemes.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    super::{
        export::ProjKey,
        origin_evidence::SourceCallee,
        ownership_access::{Expression, OperandSyntax, PlaceSyntax},
        ownership_boundary::{self, Role, Variables, Window},
        ownership_occurrence::{self, Availability::Present, PathStep},
    },
    facts::{EquationId, Facts},
    transport::{CandidateGraph, Edge, Evidence, Node, Rule},
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Action {
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) kind: String,
    pub(crate) equations: Vec<EquationId>,
    pub(crate) zero_requirements: Vec<Node>,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct PackedReturn {
    pub(crate) root: Node,
    pub(crate) components: Vec<(Vec<PathStep>, Node)>,
    pub(crate) carrier_input: Node,
    /// Required owning declaration scheme, not an observed model decision.
    pub(crate) field_scheme: String,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Proof {
    pub(crate) construction: u32,
    pub(crate) function: String,
    pub(crate) parameter: u32,
    pub(crate) structure: String,
    pub(crate) entry_boundary: usize,
    pub(crate) entry_version: u32,
    pub(crate) input_components: Vec<(Vec<PathStep>, Node)>,
    pub(crate) required_guards: Vec<(EquationId, bool)>,
    pub(crate) used_fields: Vec<String>,
    pub(crate) actions: Vec<Action>,
    pub(crate) packed_return: Option<PackedReturn>,
    pub(crate) terminal_inventory: Vec<usize>,
}
/// R329-2: which gate refused, so `Unsupported` reads as a gate rather than a
/// wall. `SingleDescendantOnly` is the width limit R317-2 deferred, named so it
/// can be counted at the first measurement.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Site {
    RouteCycle,
    PathWithoutReturn,
    ParameterIndex,
    MultipleOwningParameters,
    ParameterNotRawPointer,
    PointeeNotStruct,
    GenericFieldDeclaration,
    HeterogeneousPointerField,
    SinkNotFree,
    SingleDescendantOnly,
    ReturnTypeMismatch,
    ForeignCallNotSink,
    UnsupportedExpression,
    NonPointerDestinationWithSource,
    SourceOperandMissing,
    /// R337-3(ii): a cell of a landed or returned object whose token was
    /// consumed and never put back. In C the cell still holds what was read out
    /// of it; the model consumes on read and the emitted owning form moves the
    /// token, so a later read sees a value there and nothing here. That
    /// divergence is outside §28, so it refuses. A null store counts as a
    /// refill.
    ConsumedCellNotRefilled,
    /// R336-2: a view freed. The callee only LENT the component, so the caller
    /// still owns it and still reaches it; freeing the view frees a subtree the
    /// caller is responsible for, and on the emitted side it is a `free`
    /// through what became a borrow into a `Box`.
    SinkOnView,
    /// R335-4: a view stored into an owning cell. The callee only LENT the
    /// component, so the caller still owns it; writing the view back makes the
    /// cell name a node inside its own old generation, and the emitted
    /// overwrite drops that generation while the cell still points into it.
    ViewStoredIntoOwningCell,
    /// R319-3's owed split: a store into a pointer field of the certified
    /// structure, reached through the certified root. This is the
    /// DEFERRED-G-FIELD-IN-CERTIFICATE case — W-CF-5's second destination and
    /// (b)'s `root->left = insert(root->left, key)` — and it is a deferral, not
    /// an escape. Named so the two are counted apart at the first measurement.
    FieldStoreDeferred,
}

/// Why an edge carried no usable transfer. Each variant is one condition in
/// the edge loop, named where it is decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum TransferGap {
    /// The edge's evidence is neither a transfer nor a frame equation.
    EdgeIsNotATransfer,
    /// The transfer names a source or a destination that is not present.
    EndpointAbsent,
    /// No `assume(destination_use = false)` equation accompanies the transfer.
    DestinationNotAssumedZero,
    /// A by-move `equal` transfer with no `assume(source_def = false)`.
    SourceNotAssumedZero,
    /// The edge's target is neither end of the transfer it carries.
    EdgeEndpointOutsideTransfer,
    /// A landing's transfer has no present destination to carry the component.
    LandingDestinationAbsent,
    /// A depth-0 store the certificate cannot account for as a transfer or a
    /// registered proxy. Carries the store, because a fix needs to know which
    /// one — R325-1's structured receipt, as `AmbiguousRoute` carries its ends.
    StoreNotCovered { block: u32, statement: usize },
    /// The store is covered, but one of its two consume records is absent.
    ConsumeRecordAbsent,
    /// A covered store whose consume records carry no projected window.
    ConsumeWindowAbsent,
    /// No component law for one offset of a covered store's window.
    ComponentLawAbsent,
    /// A component law with no `assume(destination_use = false)`.
    ComponentDestinationNotAssumedZero,
    /// A by-move component law with no `assume(source_def = false)`.
    ComponentSourceNotAssumedZero,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Error {
    Unsupported(Site),
    /// R332-2: the line that refused. `Coverage` reaches here from 36 explicit
    /// sites and from every `one()` call, so naming them by hand would have
    /// missed the helper entirely; `#[track_caller]` attributes those to their
    /// caller instead.
    Coverage(u32),
    ParentFreeWithLiveDescendant,
    CompetingDisposition,
    UnaccountedToken,
    /// The single positive route forks or dead-ends: the value reaches more than
    /// one place, or none. Distinct from UnaccountedToken, which is a return
    /// that does not account for every input component. Carries the choice count
    /// so the refusal says which, per R325-1's structured receipt.
    AmbiguousRoute {
        choices: usize,
        from: Node,
        to: Node,
    },
    /// Retained so an entry written before R350-3 still decodes its own
    /// recorded reason. Nothing emits it any more.
    MissingTransfer,
    /// R350-3(2): twelve distinct conditions returned `MissingTransfer` with no
    /// way to tell them apart from a recorded entry. The gap says which.
    MissingTransferGap(TransferGap),
    BoundaryCoverage,
    FrameCoverage,
    /// R317-1: each path certifies, but their boundary summaries are not one
    /// contract.
    BoundaryDisagreement,
    /// R317-2: the per-path core keeps one sink per path.
    MultipleSinks,
    /// R315-2: more CFG paths than the budget admits.
    PathBudget,
    /// R310-1: a loop whose body performs a consuming token operation. Only a
    /// loop that leaves every token untouched is admitted, and then it is not
    /// traversed, because it cannot change what the paths carry.
    LoopWithTokenOperation,
    /// A store through a dereference into a pointer location that is NOT a
    /// field of the certified structure reached through the certified root: a
    /// global, or a field of some other object. That is an escape and stays
    /// refused. The G-FIELD subset this gate used to cover as well now refuses
    /// `Unsupported(FieldStoreDeferred)` instead.
    PointerDestinationStore,
}
#[track_caller]
fn one<T>(items: impl IntoIterator<Item = T>) -> Result<T, Error> {
    let at = std::panic::Location::caller().line();
    let mut items = items.into_iter();
    let value = items.next().ok_or(Error::Coverage(at))?;
    if items.next().is_some() {
        return Err(Error::Coverage(at));
    }
    Ok(value)
}
fn operand(value: &OperandSyntax) -> Option<&PlaceSyntax> {
    match value {
        OperandSyntax::Copy { place } | OperandSyntax::Move { place } => Some(place),
        _ => None,
    }
}

fn internal_boundaries_complete(
    facts: &Facts,
    construction: u32,
    function: &str,
) -> Result<(), Error> {
    let window = |w: &super::super::ownership_occurrence::Availability<Window>| match w {
        Present(Window::Single { start, end }) => (*start..*end).collect::<Vec<_>>(),
        Present(Window::UseDef {
            use_start,
            use_end,
            def_start,
            def_end,
        }) => (*use_start..*use_end).chain(*def_start..*def_end).collect(),
        _ => Vec::new(),
    };
    let variables = |v: &Variables| match *v {
        Variables::Single { var } => vec![var],
        Variables::UseDef { use_var, def_var } => vec![use_var, def_var],
    };
    for boundary in facts.boundary_substitutions.iter().filter(|b| {
        b.point.construction == construction
            && b.point.function.as_deref() == Some(function)
            && matches!(b.role, Role::Entry | Role::ExitReturn | Role::ExitOutput)
    }) {
        let expected_actual = window(&boundary.actual);
        let expected_formal = window(&boundary.formal);
        let actual: Vec<_> = boundary
            .matched
            .iter()
            .flat_map(|p| variables(&p.actual))
            .collect();
        let formal: Vec<_> = boundary
            .matched
            .iter()
            .flat_map(|p| variables(&p.formal))
            .collect();
        let set = |v: &Vec<u32>| v.iter().copied().collect::<BTreeSet<_>>();
        if !boundary.unmatched_actual_vars.is_empty()
            || !boundary.unmatched_formal_vars.is_empty()
            || set(&actual) != set(&expected_actual)
            || actual.len() != expected_actual.len()
            || set(&formal) != set(&expected_formal)
            || formal.len() != expected_formal.len()
            || set(&actual).len() != actual.len()
            || set(&formal).len() != formal.len()
        {
            return Err(Error::BoundaryCoverage);
        }
    }
    Ok(())
}

// Projection framing belongs to the full internal certificate, including
// components that currently carry zero and never enter a positive route.
fn projection_frames(
    facts: &Facts,
    construction: u32,
    function: &str,
    order: &BTreeMap<u32, usize>,
) -> Result<Vec<Action>, Error> {
    let mut actions = Vec::new();
    for consume in facts.consumes.iter().filter(|c| {
        c.point.construction == construction
            && c.point.function.as_deref() == Some(function)
            && c.point
                .block
                .is_some_and(|block| order.contains_key(&block))
    }) {
        let Present(base) = &consume.base else { continue };
        for (pre, post) in (base.use_start..base.use_end).zip(base.def_start..base.def_end) {
            if matches!(&consume.projected, Present(projected)
                if (projected.use_start..projected.use_end).contains(&pre))
            {
                continue;
            }
            let equations: Vec<_> = facts
                .equations
                .iter()
                .filter(|e| {
                    e.point == consume.point
                        && e.transfer.is_none()
                        && e.operation == "equal"
                        && e.variables == [pre, post]
                })
                .map(|e| EquationId {
                    construction,
                    ordinal: e.ordinal,
                })
                .collect();
            if equations.is_empty() {
                return Err(Error::FrameCoverage);
            }
            let action = Action {
                block: consume.point.block.ok_or(Error::FrameCoverage)?,
                statement: consume.point.statement.ok_or(Error::FrameCoverage)?,
                kind: "projection-frame".into(),
                equations,
                zero_requirements: vec![],
            };
            if !actions.contains(&action) {
                actions.push(action);
            }
        }
    }
    Ok(actions)
}

/// Backward demand selects one exact successor at every split. The returned
/// edges still require their guard polarities and unselected-partner zeros.
fn route<'a>(edges: &'a [&'a Edge], start: Node, terminal: Node) -> Result<Vec<&'a Edge>, Error> {
    let mut reaches = BTreeSet::from([terminal]);
    loop {
        let before = reaches.len();
        for edge in edges {
            if reaches.contains(&edge.to) {
                reaches.insert(edge.from);
            }
        }
        if reaches.len() == before {
            break;
        }
    }
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    let mut current = start;
    while current != terminal {
        if !seen.insert(current) {
            return Err(Error::Unsupported(Site::RouteCycle));
        }
        let mut choices = Vec::new();
        for &edge in edges
            .iter()
            .filter(|edge| edge.from == current && reaches.contains(&edge.to))
        {
            if !choices.contains(&edge) {
                choices.push(edge);
            }
        }
        if choices.len() != 1 {
            return Err(Error::AmbiguousRoute {
                choices: choices.len(),
                from: current,
                to: terminal,
            });
        }
        let edge = choices[0];
        result.push(edge);
        current = edge.to;
    }
    Ok(result)
}

pub(crate) fn certify_linear(
    facts: &Facts,
    construction: u32,
    function: &str,
    parameter: u32,
) -> Result<Proof, Error> {
    certify_linear_metadata(
        facts,
        construction,
        function,
        parameter,
        &super::matched::guard_aliases(&facts.guards),
    )
}

/// Does any block in this range perform an operation that moves or ends a
/// token? A borrowing read does not; a free and a store into memory do.
///
/// Keyed on the destination PLACE. A non-empty destination PATH is the
/// component of a component-wise copy — `node = (*node).child` produces one
/// whose path is `[Deref, Field child]` — so reading the path here called
/// every pointer copy consuming, which is what held the view walk. A store
/// into a field is a destination place with a non-empty projection.
/// (`8b76fc63`'s message states this correction; its diff does not carry it.)
fn consuming_operation(facts: &Facts, construction: u32, function: &str, blocks: &[u32]) -> bool {
    facts.equations.iter().any(|e| {
        e.point.construction == construction
            && e.point.function.as_deref() == Some(function)
            && e.point.block.is_some_and(|b| blocks.contains(&b))
            && (e.operation == "sink"
                || e.transfer.as_ref().is_some_and(
                    |t| matches!(&t.destination, Present(d) if !d.projection.is_empty()),
                ))
    })
}

/// Does this call receive no owning argument at all? Then whatever it returns
/// is not one of the caller's tokens, whatever else it may be. Read off the
/// `CallArgument` rows at the same point: an argument with no ownership window
/// carries no token.
fn takes_no_owning_argument(
    boundaries: &[ownership_boundary::Substitution],
    receiver: &ownership_boundary::Substitution,
) -> bool {
    !boundaries.iter().any(|b| {
        b.role == Role::CallArgument
            && b.point == receiver.point
            && b.callee == receiver.callee
            && matches!(&b.actual, Present(_))
    })
}

/// R317-2's must-answer for W-CF-6: which pointer fields of the certified
/// parameter this path proves null. A null pointer carries no token, so a
/// component proven null before the parent's free owes neither a take nor a
/// pre-free zero — which is what `deleteNode`'s one-child arm rests on.
///
/// Every link is recorded evidence, none of it inferred. The block's `switch`
/// says what it branched on and names its arms; the arm this path takes is the
/// one whose target is the path's next block; the discriminant's definition is
/// an `is_null` call from `readonly_intrinsics`, the same set the call gate
/// admits; and that call's argument is a copy of a component of the parameter.
/// Each lookup is a `one()`, so a second definition of either temporary on the
/// path refuses rather than picks. Returns the field index against the position
/// of the test, since a fact proves nothing about what happens before it.
fn path_null_fields(
    roster: &super::coverage::BodyRoster,
    body: &super::readers::Body,
    order: &BTreeMap<u32, usize>,
    parameter: u32,
) -> Result<BTreeMap<Option<u32>, (usize, usize)>, Error> {
    let mut path: Vec<_> = order.iter().map(|(block, at)| (*at, *block)).collect();
    path.sort_unstable();
    let mut proven = BTreeMap::new();
    for window in path.windows(2) {
        let [(_, block), (_, next)] = window else {
            return Err(Error::Coverage(line!()));
        };
        let data = one(roster.blocks.iter().filter(|b| b.block == *block))?;
        let Some(switch) = &data.switch else { continue };
        let Some(discriminant) = switch.discriminant else {
            continue;
        };
        // The true arm of a two-armed `bool` switch, and nothing else. MIR
        // writes that as `[(Some(0), false arm), (None, true arm)]`, so the
        // otherwise arm is the one `is_null` returning true selects.
        let mut arms = switch.targets.iter().filter(|(_, target)| target == next);
        let Some((value, _)) = arms.next() else { continue };
        if arms.next().is_some() || switch.targets.len() != 2 || value.is_some() {
            continue;
        }
        let test = one(body.occurrences.iter().filter(|o| {
            order.contains_key(&o.site.block)
                && o.syntax.destination.local == discriminant
                && o.syntax.destination.projection.is_empty()
        }))?;
        if !body.readonly_intrinsic(test.site.block, test.site.statement) {
            continue;
        }
        let Expression::Call { operands } = &test.syntax.expression else {
            continue;
        };
        let [argument] = operands.as_slice() else { continue };
        let Some(argument) = operand(argument) else { continue };
        if !argument.projection.is_empty() {
            continue;
        }
        let feed = one(body
            .occurrences
            .iter()
            .filter(|o| order.contains_key(&o.site.block) && o.syntax.destination == *argument))?;
        let Expression::Value { operand: value } = &feed.syntax.expression else {
            continue;
        };
        let Some(place) = operand(value) else { continue };
        // `None` is the root itself — bst's `if (node == NULL)` — and
        // `Some(index)` one of its pointer fields.
        let component = match place.projection.as_slice() {
            [] => None,
            [ProjKey::Deref, ProjKey::Field(index)] => Some(*index),
            _ => continue,
        };
        if place.local != parameter {
            continue;
        }
        let at = (
            *order
                .get(&test.site.block)
                .ok_or(Error::Coverage(line!()))?,
            test.site.statement,
        );
        if proven.insert(component, at).is_some_and(|old| old != at) {
            return Err(Error::Coverage(line!()));
        }
    }
    Ok(proven)
}

/// R315-2: every CFG path from entry to a return. A back edge is admitted only
/// when the loop it closes performs no consuming token operation, and is then
/// not traversed; any other loop is a typed hold.
fn enumerate_paths(
    facts: &Facts,
    construction: u32,
    function: &str,
    roster: &super::coverage::BodyRoster,
) -> Result<Vec<Vec<u32>>, Error> {
    const BUDGET: usize = 64;
    let mut complete: Vec<Vec<u32>> = Vec::new();
    let mut pending = vec![vec![0u32]];
    while let Some(path) = pending.pop() {
        if complete.len() + pending.len() > BUDGET {
            return Err(Error::PathBudget);
        }
        let current = *path.last().ok_or(Error::Coverage(line!()))?;
        let data = one(roster
            .blocks
            .iter()
            .filter(|b| b.block == current && b.reachable))?;
        match data.successors.as_slice() {
            [] if data.return_statement.is_some() => complete.push(path),
            [] => return Err(Error::Unsupported(Site::PathWithoutReturn)),
            successors => {
                for &next in successors {
                    if let Some(start) = path.iter().position(|b| *b == next) {
                        if consuming_operation(facts, construction, function, &path[start..]) {
                            return Err(Error::LoopWithTokenOperation);
                        }
                        continue;
                    }
                    let mut extended = path.clone();
                    extended.push(next);
                    pending.push(extended);
                }
            }
        }
    }
    if complete.is_empty() {
        return Err(Error::Coverage(line!()));
    }
    Ok(complete)
}

/// R319-4/R320-3: the `phase == "phi"` equations this path admits. Neither the
/// equation nor the phi edge names the predecessor, so it is recovered through
/// the version table: an input variable belongs to exactly one `(local, ssa)`,
/// and `(to, local, input_ssa)` selects the edge that carries `from`. Fails
/// closed if a variable is ever found in two versions.
fn phi_selection(
    facts: &Facts,
    construction: u32,
    function: &str,
    roster: &super::coverage::BodyRoster,
    path: &[u32],
) -> Result<BTreeSet<usize>, Error> {
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == construction && p.function.as_deref() == Some(function)
    };
    let mut owner: BTreeMap<u32, (u32, u32)> = BTreeMap::new();
    for version in &roster.versions {
        for &var in &version.variables {
            if owner.insert(var, (version.local, version.ssa)).is_some() {
                return Err(Error::Coverage(line!()));
            }
        }
    }
    let mut admitted = BTreeSet::new();
    for (index, &to) in path.iter().enumerate() {
        for phi in roster.phis.iter().filter(|p| p.block == to) {
            let from = *path
                .get(index.checked_sub(1).ok_or(Error::Coverage(line!()))?)
                .ok_or(Error::Coverage(line!()))?;
            let supplied: BTreeSet<_> = facts
                .phi_edges
                .iter()
                .filter(|e| scope(&e.point) && e.to == to && e.local == phi.local && e.from == from)
                .map(|e| e.input_ssa)
                .collect();
            let [input_ssa] = supplied.iter().copied().collect::<Vec<_>>()[..] else {
                return Err(Error::Coverage(line!()));
            };
            for equation in facts.equations.iter().filter(|e| {
                scope(&e.point)
                    && e.point.phase == "phi"
                    && e.point.block == Some(to)
                    && e.operation == "equal"
                    && e.transfer.is_none()
                    && e.variables.len() == 2
            }) {
                if owner.get(&equation.variables[1]) == Some(&(phi.local, input_ssa)) {
                    admitted.insert(equation.ordinal);
                }
            }
        }
    }
    Ok(admitted)
}

pub(crate) fn certify_linear_metadata(
    facts: &Facts,
    construction: u32,
    function: &str,
    parameter: u32,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<Proof, Error> {
    certify_visiting(
        facts,
        construction,
        function,
        parameter,
        aliases,
        &BTreeSet::new(),
    )
}

/// `visiting` carries the functions whose certificates are already being
/// established further up. A callee already in it gets no contract, which is
/// what makes mutual recursion terminate rather than descend; the function
/// under proof is the exception, since assuming its own contract is the whole
/// of R310-2.
fn certify_visiting(
    facts: &Facts,
    construction: u32,
    function: &str,
    parameter: u32,
    aliases: &BTreeMap<EquationId, EquationId>,
    visiting: &BTreeSet<String>,
) -> Result<Proof, Error> {
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == construction && p.function.as_deref() == Some(function)
    };
    let roster = one(facts.body_rosters.iter().filter(|r| scope(&r.point)))?;
    let paths = enumerate_paths(facts, construction, function, roster)?;
    let mut proofs = Vec::new();
    for path in &paths {
        let order: BTreeMap<u32, usize> = path
            .iter()
            .copied()
            .enumerate()
            .map(|(position, block)| (block, position))
            .collect();
        let admitted = phi_selection(facts, construction, function, roster, path)?;
        proofs.push(certify_path(
            facts,
            construction,
            function,
            parameter,
            aliases,
            &order,
            &admitted,
            visiting,
        )?);
    }
    let [first, rest @ ..] = proofs.as_slice() else { return Err(Error::Coverage(line!())) };
    // R321-3: which object the returned token names is not a component of the
    // boundary. Only whether a token comes back, and how many.
    if rest.iter().any(|proof| {
        proof.parameter != first.parameter
            || proof.input_components != first.input_components
            || proof.structure != first.structure
            || proof.entry_boundary != first.entry_boundary
            || proof.entry_version != first.entry_version
            || proof.terminal_inventory != first.terminal_inventory
    }) {
        return Err(Error::BoundaryDisagreement);
    }
    let mut merged = proofs
        .iter()
        .find(|proof| proof.packed_return.is_some())
        .unwrap_or(first)
        .clone();
    for proof in &proofs {
        merged.actions.extend(proof.actions.iter().cloned());
        merged.used_fields.extend(proof.used_fields.iter().cloned());
        for (key, value) in &proof.required_guards {
            if let Some(old) = merged
                .required_guards
                .iter()
                .find(|(existing, _)| existing == key)
            {
                if old.1 != *value {
                    return Err(Error::CompetingDisposition);
                }
            } else {
                merged.required_guards.push((*key, *value));
            }
        }
    }
    merged
        .actions
        .sort_by_key(|action| (action.block, action.statement, action.kind.clone()));
    merged.actions.dedup();
    merged.used_fields.sort();
    merged.used_fields.dedup();
    merged.required_guards.sort();
    merged.required_guards.dedup();
    Ok(merged)
}

fn certify_path(
    facts: &Facts,
    construction: u32,
    function: &str,
    parameter: u32,
    aliases: &BTreeMap<EquationId, EquationId>,
    order: &BTreeMap<u32, usize>,
    admitted_phis: &BTreeSet<usize>,
    visiting: &BTreeSet<String>,
) -> Result<Proof, Error> {
    internal_boundaries_complete(facts, construction, function)?;
    let frames = projection_frames(facts, construction, function, order)?;
    let terminal_inventory = super::fold_coverage::validate(facts, construction, function)
        .map_err(|_| Error::Coverage(line!()))?;
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == construction && p.function.as_deref() == Some(function)
    };
    let roster = one(facts.body_rosters.iter().filter(|r| scope(&r.point)))?;
    if parameter == 0 || parameter as usize > roster.argument_count {
        return Err(Error::Unsupported(Site::ParameterIndex));
    }
    if roster.versions.iter().any(|version| {
        version.local != parameter
            && version.local > 0
            && version.local as usize <= roster.argument_count
            && version.definition == super::coverage::DefinitionKind::Entry
            && !version.variables.is_empty()
    }) {
        return Err(Error::Unsupported(Site::MultipleOwningParameters));
    }
    let body = one(facts
        .reader_inputs
        .bodies
        .iter()
        .filter(|b| b.function == function))?;
    if !body.complete_operations
        || facts.source_occurrences.get(function) != Some(&body.occurrences)
    {
        return Err(Error::Coverage(line!()));
    }
    let types = facts.fold_types.as_ref().ok_or(Error::Coverage(line!()))?;
    let place_type = |place: &PlaceSyntax| {
        one(types
            .places
            .iter()
            .filter(|p| p.function == function && &p.place == place))
    };
    let root = place_type(&PlaceSyntax {
        local: parameter,
        projection: vec![],
    })?;
    if !matches!(
        root.pointer,
        Some(super::fold_types::PointerFlavor::RawConst | super::fold_types::PointerFlavor::RawMut)
    ) {
        return Err(Error::Unsupported(Site::ParameterNotRawPointer));
    }
    let structure = root
        .pointee_struct
        .as_ref()
        .ok_or(Error::Unsupported(Site::PointeeNotStruct))?;
    let declaration = one(types.structures.iter().filter(|s| &s.identity == structure))?;
    // The initial certificate does not instantiate generic field declarations.
    if root.pointee_type.as_ref() != Some(&declaration.declared_type) {
        return Err(Error::Unsupported(Site::GenericFieldDeclaration));
    }
    let entry = one(facts.boundary_substitutions.iter().filter(|b| {
        scope(&b.point) && b.role == Role::Entry && b.formal_local == Some(parameter)
    }))?;
    let Present(Window::Single { start, end }) = &entry.actual else {
        return Err(Error::Coverage(line!()));
    };
    let initial = one(roster.versions.iter().filter(|v| {
        v.local == parameter && v.definition == super::coverage::DefinitionKind::Entry
    }))?;
    if initial.variables.iter().copied().ne(*start..*end) {
        return Err(Error::Coverage(line!()));
    }
    let terminals: Vec<_> = facts
        .terminals
        .iter()
        .filter(|t| scope(&t.point) && t.point.block.is_none_or(|block| order.contains_key(&block)))
        .cloned()
        .collect();
    let parameter_exit = one(terminals.iter().filter(|t| t.local == parameter))?;
    let Present(values) = &parameter_exit.values else { return Err(Error::Coverage(line!())) };
    let paths: Vec<_> = values
        .iter()
        .map(|v| match &v.path {
            Present(path) => Ok(path.clone()),
            _ => Err(Error::Coverage(line!())),
        })
        .collect::<Result<_, _>>()?;
    let mut expected = vec![vec![]];
    for field in declaration.fields.iter().filter(|f| f.pointer.is_some()) {
        if field.pointee_struct.as_ref() != Some(structure)
            || field.pointee_type != root.pointee_type
        {
            return Err(Error::Unsupported(Site::HeterogeneousPointerField));
        }
        expected.push(vec![
            PathStep::Deref,
            PathStep::Field {
                structure: structure.clone(),
                index: field.index,
                name: field.name.clone(),
            },
        ]);
    }
    if paths != expected || paths.len() != initial.variables.len() {
        return Err(Error::Coverage(line!()));
    }
    // The path's own rows, not the function's. Without this a selection such as
    // `taking` sees the other path's take as well and `one()` reports Coverage,
    // which is what W-CF-1 was refusing on. A point with no block belongs to
    // every path; a phi equation belongs only to the path that admitted it.
    let on_path = |p: &super::super::ownership_evidence::Point| {
        scope(p) && p.block.is_none_or(|block| order.contains_key(&block))
    };
    let consumes: Vec<_> = facts
        .consumes
        .iter()
        .filter(|c| on_path(&c.point))
        .cloned()
        .collect();
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|e| {
            on_path(&e.point) && (e.point.phase != "phi" || admitted_phis.contains(&e.ordinal))
        })
        .cloned()
        .collect();
    let boundaries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|b| on_path(&b.point))
        .cloned()
        .collect();
    let registrations: Vec<_> = facts
        .call_arg_registrations
        .iter()
        .filter(|r| on_path(&r.point))
        .cloned()
        .collect();
    ownership_occurrence::validate(function, &consumes, &equations)
        .map_err(|_| Error::Coverage(line!()))?;
    ownership_boundary::validate_links(
        function,
        &boundaries,
        &registrations,
        &consumes,
        &equations,
    )
    .map_err(|_| Error::Coverage(line!()))?;
    if equations.iter().any(|e| e.validate().is_err()) {
        return Err(Error::Coverage(line!()));
    }
    if equations.iter().any(|e| {
        (e.operation.starts_with("guarded-") || e.endpoint.is_some())
            && !aliases.contains_key(&EquationId {
                construction,
                ordinal: e.ordinal,
            })
    }) {
        return Err(Error::Coverage(line!()));
    }
    // Independent source coverage catches escaping stores absent from the graph.
    // R319-3's split: a store into a pointer field of the certified structure,
    // written through the certified root itself, is the deferred G-FIELD case
    // and says so; every other pointer destination is an escape.
    for occurrence in &body.occurrences {
        if !order.contains_key(&occurrence.site.block) {
            continue;
        }
        let destination = &occurrence.syntax.destination;
        if destination.projection.is_empty() || place_type(destination)?.pointer.is_none() {
            continue;
        }
        // Keyed on the structure being written, not on which local reaches it:
        // W-CF-5 stores through the taken descendant and `insert` stores through
        // the parameter, and both are the same deferred case. Whether the base
        // is a token this certificate accounts for is the admission question,
        // not the classification one — and both arms refuse either way, so the
        // split can only move a refusal's name, never its verdict.
        let base = place_type(&PlaceSyntax {
            local: destination.local,
            projection: vec![],
        })?;
        if base.pointee_struct.as_ref() == Some(structure)
            && matches!(destination.projection.as_slice(), [ProjKey::Deref, ProjKey::Field(index)]
                if declaration
                    .fields
                    .iter()
                    .any(|field| field.index == *index && field.pointer.is_some()))
        {
            // Admitted here and accounted for below: a field store's own
            // occurrence still has to be covered by a selected transfer, and
            // an unaccounted one refuses `FieldStoreDeferred` there. Refusing
            // it at this gate would refuse it before the route exists.
            continue;
        }
        return Err(Error::PointerDestinationStore);
    }
    let graph =
        CandidateGraph::build_metadata(facts, aliases).map_err(|_| Error::Coverage(line!()))?;
    // R310-2, assume-guarantee: a call to the function under proof carries the
    // contract being proved, so the token that goes in is the token that comes
    // back and the callee's body is never traversed. Only the root component is
    // paired: the argument's own window is one slot wide, the callee's deeper
    // components being its business and not this caller's. A call to anything
    // else is not admitted here — its contract is not the one being assumed.
    let mut assumed = Vec::new();
    // A callee whose contract this certificate may assume: the function under
    // proof, by R310-2; or any other function that has a certificate of its
    // own, established here rather than taken on trust. `visiting` stops a
    // cycle from descending, and the depth bound stops a long chain from
    // costing more than it is worth — both fail closed, since a callee with no
    // contract gets no edge and the route is what refuses.
    const CALLEE_DEPTH: usize = 4;
    let licensed = |callee: &str, formal: Option<u32>| -> bool {
        if callee == function {
            return true;
        }
        if visiting.contains(callee) || visiting.len() >= CALLEE_DEPTH {
            return false;
        }
        let Some(formal) = formal else { return false };
        let mut deeper = visiting.clone();
        deeper.insert(function.to_string());
        certify_visiting(facts, construction, callee, formal, aliases, &deeper).is_ok()
    };
    // R335-4: does this callee LEND the argument rather than take it? Then the
    // caller keeps its token across the call — a frame on the argument, exactly
    // the shape a read-only intrinsic's lend takes — and what comes back is a
    // view, which owns nothing.
    let lends = |callee: &str, index: Option<usize>| {
        index.is_some_and(|index| facts.reader_plan.lends_parameter(callee, index))
    };
    let mut views: BTreeSet<Node> = BTreeSet::new();
    for argument in boundaries.iter().filter(|b| {
        b.role == Role::CallArgument
            && b.callee.as_deref().is_some_and(|callee| {
                lends(callee, b.argument_index) || licensed(callee, b.formal_local)
            })
    }) {
        let receiver = one(boundaries.iter().filter(|b| {
            b.role == Role::ReturnReceiver
                && b.callee == argument.callee
                && b.point == argument.point
        }))?;
        // An argument with no ownership window carries no token — `insert`'s
        // `key` is an `i32`. Skipping it is fail-closed: a pointer argument
        // that somehow had no window would leave the route with no edge to
        // take, and the route is what refuses.
        let Present(actual) = &argument.actual else { continue };
        let (
            Window::UseDef {
                use_start,
                use_end,
                def_start: argument_def,
                ..
            },
            Present(Window::UseDef {
                def_start,
                def_end: receiver_end,
                ..
            }),
        ) = (actual, &receiver.actual)
        else {
            return Err(Error::Coverage(line!()));
        };
        if argument
            .callee
            .as_deref()
            .is_some_and(|callee| lends(callee, argument.argument_index))
        {
            for slot in 0..(use_end - use_start) {
                assumed.push(Edge {
                    from: Node {
                        construction,
                        var: use_start + slot,
                    },
                    to: Node {
                        construction,
                        var: argument_def + slot,
                    },
                    rule: Rule::Frame,
                    evidence: Evidence::Boundary {
                        construction,
                        ordinal: argument.ordinal,
                        matched: slot as usize,
                    },
                    guard: None,
                });
            }
            views.extend((*def_start..*receiver_end).map(|var| Node { construction, var }));
            continue;
        }
        assumed.push(Edge {
            from: Node {
                construction,
                var: *use_start,
            },
            to: Node {
                construction,
                var: *def_start,
            },
            rule: Rule::Copy,
            evidence: Evidence::Boundary {
                construction,
                ordinal: argument.ordinal,
                matched: 0,
            },
            guard: None,
        });
    }
    let local_edges: Vec<_> = graph
        .edges
        .iter()
        .filter(|edge| match edge.evidence {
            // A phi edge is how a value crosses a merge block. `equations` is
            // already restricted to this path's admitted phis, so admitting the
            // rule here is automatically path-selective. Without it a route
            // through any merge dead-ends, which is the `choices: 0` the three
            // witnesses were reporting.
            Evidence::Transfer(id) | Evidence::Frame { equation: id, .. } | Evidence::Phi(id) => {
                id.construction == construction
                    && equations.iter().any(|e| e.ordinal == id.ordinal)
                    && matches!(edge.rule, Rule::Copy | Rule::Frame | Rule::Phi)
            }
            _ => false,
        })
        .chain(assumed.iter())
        .collect();
    // A view owns nothing, so it may not become an owning cell's content. Read
    // through the graph rather than off the store alone, since the view can
    // reach the store through any number of copies first.
    loop {
        let before = views.len();
        for edge in &local_edges {
            if views.contains(&edge.from) {
                views.insert(edge.to);
            }
        }
        if views.len() == before {
            break;
        }
    }
    if equations.iter().any(|e| {
        e.transfer.as_ref().is_some_and(|t| {
            matches!(&t.destination, Present(destination) if !destination.projection.is_empty())
                && views.contains(&Node {
                    construction,
                    var: t.source_use,
                })
        })
    }) {
        return Err(Error::Unsupported(Site::ViewStoredIntoOwningCell));
    }
    let sinks: Vec<_> = graph
        .sinks
        .iter()
        .filter(|s| {
            s.node.construction == construction
                && s.endpoint.function == function
                && order.contains_key(&s.endpoint.block)
        })
        .collect();
    if sinks.len() > 1 {
        return Err(Error::MultipleSinks);
    }
    // R336-2: and a view may not be sunk either. Without this the shape refuses
    // only because the route happens to dead-end, which is not the reason.
    if sinks.iter().any(|sink| views.contains(&sink.node)) {
        return Err(Error::Unsupported(Site::SinkOnView));
    }
    let returned = one(terminals.iter().filter(|t| t.local == 0))?;
    let return_values = match &returned.values {
        Present(v) => v.as_slice(),
        _ => &[],
    };
    let node = |var| Node { construction, var };
    let inputs: Vec<_> = paths
        .iter()
        .cloned()
        .zip(initial.variables.iter().copied().map(node))
        .collect();
    let mut proof = Proof {
        construction,
        function: function.into(),
        parameter,
        structure: structure.clone(),
        entry_boundary: entry.ordinal,
        entry_version: initial.ssa,
        input_components: inputs.clone(),
        required_guards: vec![],
        used_fields: vec![],
        actions: frames,
        packed_return: None,
        terminal_inventory,
    };
    let null_fields = path_null_fields(roster, body, order, parameter)?;
    let live: Vec<_> = inputs
        .iter()
        .skip(1)
        .filter(|(path, _)| {
            !matches!(&path[1], PathStep::Field { index, .. }
                if null_fields.contains_key(&Some(*index)))
        })
        .collect();
    // R310-2: a path that proved the parameter null carries no token in any of
    // its components, so the token it returns cannot be one of them. It has to
    // come from somewhere that took nothing from us — a call on this path with
    // no owning argument at all cannot be handing one of our components back —
    // and the route is re-rooted there rather than waived. This is bst's
    // `if (node == NULL) return newNode(key);`.
    // Available, not required: `deleteMaybe` proves its root null and returns
    // that same null root, which routes from the input as usual. The fresh
    // source is the alternative start for a path that returns something else.
    let fresh_source = null_fields.get(&None).and_then(|_| {
        let mut receivers = boundaries.iter().filter(|b| {
            b.role == Role::ReturnReceiver
                && takes_no_owning_argument(&boundaries, b)
                && matches!(&b.actual, Present(Window::UseDef { .. }))
        });
        let receiver = receivers.next()?;
        if receivers.next().is_some() {
            return None;
        }
        let Present(Window::UseDef {
            def_start, def_end, ..
        }) = &receiver.actual
        else {
            return None;
        };
        ((def_end - def_start) as usize == inputs.len()).then_some(*def_start)
    });
    let mut selected = Vec::new();
    if let Some(sink) = sinks.first() {
        if sink.endpoint.callee != "free" || sink.endpoint.outcome.is_some() {
            return Err(Error::Unsupported(Site::SinkNotFree));
        }
        let free_at = (
            *order
                .get(&sink.endpoint.block)
                .ok_or(Error::Coverage(line!()))?,
            sink.endpoint.statement,
        );
        // A component the path proved null before the free is not live, and a
        // fact established after the free proves nothing about it.
        if null_fields.values().any(|at| *at >= free_at) {
            return Err(Error::ParentFreeWithLiveDescendant);
        }
        selected.extend(route(&local_edges, inputs[0].1, sink.node)?);
        let before =
            |e: &super::super::ownership_evidence::Point| -> Result<(usize, usize), Error> {
                Ok((
                    *order
                        .get(&e.block.ok_or(Error::Coverage(line!()))?)
                        .ok_or(Error::Coverage(line!()))?,
                    e.statement.ok_or(Error::Coverage(line!()))?,
                ))
            };
        let sink_eq = one(equations
            .iter()
            .filter(|e| e.ordinal == sink.equation.ordinal))?;
        // R317-2's width lift. Each live descendant lands in exactly one
        // component of the returned value: the carrier lands in the root, and a
        // descendant reattached into the carrier's field lands in that field's
        // component. A component no descendant claims is one the carrier
        // already held before it was taken, so its route starts at the
        // carrier's own slot — folded into the carrier, not lost. Same move as
        // the fresh source: re-root rather than waive.
        let mut claimed: BTreeSet<usize> = BTreeSet::new();
        let mut carrier_slots = None;
        for (path, input) in live.iter().copied() {
            let taking: Vec<_> = equations
                .iter()
                .filter(|e| {
                    e.transfer.as_ref().is_some_and(|t| {
                        matches!((&t.source, &t.destination), (Present(s), Present(d))
                    if &s.path == path && d.path.is_empty())
                    }) && matches!(
                        e.operation.as_str(),
                        "linear" | "equal" | "guarded-copy" | "guarded-reader-copy"
                    )
                })
                .collect();
            if taking.is_empty() {
                return Err(Error::ParentFreeWithLiveDescendant);
            }
            // Kept behind the take check: a parent freed with a descendant that
            // was never taken is `ParentFreeWithLiveDescendant`, whatever the
            // return looks like, and gf04/gf05 assert exactly that ordering.
            if return_values.is_empty() {
                return Err(Error::Unsupported(Site::SingleDescendantOnly));
            }
            let take = one(taking)?;
            let transfer = take.transfer.as_ref().unwrap();
            if before(&take.point)? >= before(&sink_eq.point)? {
                return Err(Error::ParentFreeWithLiveDescendant);
            }
            let carries = |k: usize| {
                route(&local_edges, *input, node(return_values[k].var)).is_ok_and(|edges| {
                    edges.iter().any(|edge| {
                        edge.evidence
                            == Evidence::Transfer(EquationId {
                                construction,
                                ordinal: take.ordinal,
                            })
                            && edge.to == node(transfer.destination_def)
                    })
                })
            };
            let landing: Vec<_> = (0..return_values.len()).filter(|k| carries(*k)).collect();
            let [landing] = landing[..] else {
                return Err(Error::Unsupported(Site::SingleDescendantOnly));
            };
            selected.append(&mut route(
                &local_edges,
                *input,
                node(return_values[landing].var),
            )?);
            if !claimed.insert(landing) {
                return Err(Error::CompetingDisposition);
            }
            let PathStep::Field { index, .. } = &path[1] else {
                return Err(Error::Coverage(line!()));
            };
            let field = one(declaration.fields.iter().filter(|f| f.index == *index))?;
            let field_scheme = field.field_key.clone().ok_or(Error::Coverage(line!()))?;
            proof.used_fields.push(field_scheme.clone());
            if landing == 0 {
                let Present(destination) = &transfer.destination else {
                    return Err(Error::MissingTransferGap(
                        TransferGap::LandingDestinationAbsent,
                    ));
                };
                let carrier = one(consumes.iter().filter(|c| c.ordinal == destination.consume))?;
                let Present(base) = &carrier.base else {
                    return Err(Error::Coverage(line!()));
                };
                if (base.def_end - base.def_start) as usize != return_values.len() {
                    return Err(Error::Coverage(line!()));
                }
                carrier_slots = Some(base.def_start);
                proof.packed_return = Some(PackedReturn {
                    root: node(return_values[0].var),
                    carrier_input: *input,
                    field_scheme,
                    components: return_values
                        .iter()
                        .skip(1)
                        .map(|value| match &value.path {
                            Present(path) => Ok((path.clone(), node(value.var))),
                            _ => Err(Error::Coverage(line!())),
                        })
                        .collect::<Result<_, _>>()?,
                });
            }
            proof.actions.push(Action {
                block: take.point.block.unwrap(),
                statement: take.point.statement.unwrap(),
                kind: "take".into(),
                equations: vec![EquationId {
                    construction,
                    ordinal: take.ordinal,
                }],
                zero_requirements: vec![node(transfer.source_def)],
            });
        }
        // No carrier means no live descendant at all — every one of them was
        // proved null — and then there is nothing of the parent's for the
        // return to have folded in.
        if let Some(base) = carrier_slots {
            for component in (0..return_values.len()).filter(|k| !claimed.contains(k)) {
                selected.extend(route(
                    &local_edges,
                    node(base + component as u32),
                    node(return_values[component].var),
                )?);
            }
        }
        proof.actions.push(Action {
            block: sink.endpoint.block,
            statement: sink.endpoint.statement,
            kind: "free".into(),
            equations: vec![sink.equation],
            zero_requirements: vec![],
        });
    } else {
        if return_values.len() != inputs.len() {
            return Err(Error::UnaccountedToken);
        }
        // The returned components are not always the inputs in the same
        // positions: a rotation permutes them, storing the parameter under its
        // own descendant and returning that descendant. The positional route is
        // tried first, so every shape that certified before certifies the same
        // way and keeps its refusal; only when it fails is the landing looked
        // for, and then it must be unique and unclaimed — a permutation, never
        // a merge.
        // A component that was never read out of its cell is still inside the
        // object it belongs to. If that object itself landed, the component
        // landed with it — G-FOLD's descendants folding into the subtree token —
        // and owes no route of its own. A component that WAS read out and still
        // has no landing is lost, and keeps its refusal.
        // Keyed on the PARAMETER's own component. Without the local, a read of
        // some other object's field of the same name counts — `rotate` reads
        // `(*y).left`, which is not `(*x).left` — and that both hid this fold
        // and admitted two shapes that must refuse.
        let consumed = |component: &Vec<PathStep>| {
            equations.iter().any(|e| {
                e.transfer.as_ref().is_some_and(|t| {
                    matches!((&t.source, &t.destination), (Present(source), Present(destination))
                        if source.local == parameter
                            && &source.path == component
                            && destination.path.is_empty())
                }) && matches!(
                    e.operation.as_str(),
                    "linear" | "equal" | "guarded-copy" | "guarded-reader-copy"
                )
            })
        };
        // ...and not overwritten. A cell that was stored into has had its old
        // content dropped, not folded, so a component with no landing whose
        // cell was overwritten is lost however untouched the old value was.
        // `crossed` and `dropIn` are exactly that and must keep refusing.
        let overwritten = |component: &Vec<PathStep>| {
            equations.iter().any(|e| {
                e.transfer.as_ref().is_some_and(|t| {
                    matches!(&t.destination, Present(destination)
                        if destination.local == parameter
                            && !destination.projection.is_empty()
                            && &destination.path == component)
                })
            })
            // R337-3(ii): a null store is a refill, and it carries no transfer,
            // so the occurrence is what says so.
            || body.occurrences.iter().any(|occurrence| {
                order.contains_key(&occurrence.site.block)
                    && occurrence.syntax.destination.local == parameter
                    && matches!(
                        (occurrence.syntax.destination.projection.as_slice(), component.as_slice()),
                        ([ProjKey::Deref, ProjKey::Field(index)], [_, PathStep::Field { index: named, .. }])
                            if index == named
                    )
            })
        };
        let mut root_landed = false;
        let returned_point = (
            returned.point.block.ok_or(Error::Coverage(line!()))?,
            returned.point.statement.ok_or(Error::Coverage(line!()))?,
        );
        let mut claimed: BTreeSet<usize> = BTreeSet::new();
        for (component, ((path, input), returned)) in inputs.iter().zip(return_values).enumerate() {
            if returned.path != Present(path.clone()) {
                return Err(Error::Coverage(line!()));
            }
            let mut landing = component;
            let mut outcome = route(&local_edges, *input, node(returned.var));
            if outcome.is_err() {
                let elsewhere: Vec<_> = (0..return_values.len())
                    .filter(|k| {
                        *k != component
                            && !claimed.contains(k)
                            && route(&local_edges, *input, node(return_values[*k].var)).is_ok()
                    })
                    .collect();
                if let [k] = elsewhere[..] {
                    landing = k;
                    outcome = route(&local_edges, *input, node(return_values[k].var));
                }
            }
            if let (Err(_), Some(base)) = (&outcome, fresh_source) {
                landing = component;
                outcome = route(
                    &local_edges,
                    node(base + component as u32),
                    node(returned.var),
                );
            }
            if outcome.is_err()
                && component > 0
                && root_landed
                && !consumed(path)
                && !overwritten(path)
            {
                proof.actions.push(Action {
                    block: returned_point.0,
                    statement: returned_point.1,
                    kind: "folded-component".into(),
                    equations: vec![],
                    zero_requirements: vec![],
                });
                continue;
            }
            selected.extend(outcome?);
            if !claimed.insert(landing) {
                return Err(Error::CompetingDisposition);
            }
            root_landed |= component == 0;
        }
        // R337-3(ii): the object is returned rather than freed, so every cell of
        // it outlives this body. A cell whose token was read out and never put
        // back still holds that token in the input and holds nothing in the
        // emitted program, which a later read would see differently.
        if let Some((path, _)) = inputs
            .iter()
            .skip(1)
            .find(|(path, _)| consumed(path) && !overwritten(path))
        {
            let _ = path;
            return Err(Error::Unsupported(Site::ConsumedCellNotRefilled));
        }
    }
    let output_type = place_type(&PlaceSyntax {
        local: 0,
        projection: vec![],
    })?;
    if output_type.pointee_type != root.pointee_type
        || output_type.pointee_struct != root.pointee_struct
    {
        return Err(Error::Unsupported(Site::ReturnTypeMismatch));
    }
    if return_values.len() != expected.len()
        || return_values
            .iter()
            .zip(&expected)
            .any(|(value, path)| value.path != Present(path.clone()))
    {
        return Err(Error::Coverage(line!()));
    }
    let mut used_equations = BTreeSet::new();
    let demanded: BTreeSet<_> = inputs
        .iter()
        .map(|(_, input)| *input)
        .chain(selected.iter().flat_map(|edge| [edge.from, edge.to]))
        .collect();
    let mut required_guards = BTreeMap::new();
    for sink in &sinks {
        required_guards.insert(
            *aliases
                .get(&sink.equation)
                .ok_or(Error::Coverage(line!()))?,
            true,
        );
    }
    for edge in selected {
        if let Some(guard) = edge.guard {
            let key = aliases
                .get(&guard.binding)
                .copied()
                .ok_or(Error::Coverage(line!()))?;
            if required_guards
                .insert(key, guard.required)
                .is_some_and(|old| old != guard.required)
            {
                return Err(Error::CompetingDisposition);
            }
        }
        // A phi merges versions; it is not a token operation, so it carries no
        // transfer and owes no old-zero. It is recorded as consumed evidence and
        // contributes no zero requirement.
        if let Evidence::Phi(id) = edge.evidence {
            used_equations.insert(id);
            continue;
        }
        // An assumed contract is recorded as an action rather than consumed
        // evidence: there is no equation behind it, which is the point.
        if let Evidence::Boundary { ordinal, .. } = edge.evidence {
            let boundary = one(boundaries.iter().filter(|b| b.ordinal == ordinal))?;
            proof.actions.push(Action {
                block: boundary.point.block.ok_or(Error::Coverage(line!()))?,
                statement: boundary.point.statement.ok_or(Error::Coverage(line!()))?,
                kind: "assumed-contract".into(),
                equations: vec![],
                zero_requirements: vec![],
            });
            continue;
        }
        let id = match edge.evidence {
            Evidence::Transfer(id) | Evidence::Frame { equation: id, .. } => id,
            _ => return Err(Error::MissingTransferGap(TransferGap::EdgeIsNotATransfer)),
        };
        used_equations.insert(id);
        let equation = one(equations.iter().filter(|e| e.ordinal == id.ordinal))?;
        let mut zeros = vec![];
        if let Some(transfer) = &equation.transfer {
            if !matches!(
                (&transfer.source, &transfer.destination),
                (Present(_), Present(_))
            ) {
                return Err(Error::MissingTransferGap(TransferGap::EndpointAbsent));
            }
            if !equations.iter().any(|e| {
                e.point == equation.point
                    && e.transfer.as_ref() == Some(transfer)
                    && e.operation == "assume"
                    && e.value == Some(false)
                    && e.variables == [transfer.destination_use]
            }) {
                return Err(Error::MissingTransferGap(
                    TransferGap::DestinationNotAssumedZero,
                ));
            }
            if transfer.by_move
                && equation.operation == "equal"
                && !equations.iter().any(|e| {
                    e.point == equation.point
                        && e.transfer.as_ref() == Some(transfer)
                        && e.operation == "assume"
                        && e.value == Some(false)
                        && e.variables == [transfer.source_def]
                })
            {
                return Err(Error::MissingTransferGap(TransferGap::SourceNotAssumedZero));
            }
            let sibling = if edge.to.var == transfer.destination_def {
                transfer.source_def
            } else if edge.to.var == transfer.source_def {
                transfer.destination_def
            } else {
                return Err(Error::MissingTransferGap(
                    TransferGap::EdgeEndpointOutsideTransfer,
                ));
            };
            zeros.push(node(sibling));
        }
        proof.actions.push(Action {
            block: equation.point.block.ok_or(Error::Coverage(line!()))?,
            statement: equation.point.statement.ok_or(Error::Coverage(line!()))?,
            kind: "transfer".into(),
            equations: vec![id],
            zero_requirements: zeros,
        });
    }
    // Every pointer-producing source row must have an authenticated selected
    // transfer, or the compiler's exact eliminated argument-proxy registration.
    for occurrence in &body.occurrences {
        if !order.contains_key(&occurrence.site.block) {
            continue;
        }
        let at = |p: &super::super::ownership_evidence::Point| {
            p.block == Some(occurrence.site.block) && p.statement == Some(occurrence.site.statement)
        };
        if let Some(callee) = &occurrence.callee {
            // A read-only intrinsic is not a token operation: `readers.rs`
            // derives the set from MIR as core/std `is_null` with a
            // non-pointer destination, and `InferMode::lend` is what the
            // inference emits for it, so the pointer crosses the call as the
            // identity edge transport now carries. This is the call in bst's
            // `if (root == NULL) return root`.
            if body.readonly_intrinsic(occurrence.site.block, occurrence.site.statement) {
                continue;
            }
            // R310-2: the self-call whose contract this certificate assumes.
            // Tied to the same evidence that built the assumed edge — the
            // `CallArgument` row for this function at this very site — so the
            // occurrence cannot be admitted unless the route could cross it.
            if matches!(callee, SourceCallee::Local(_))
                && boundaries.iter().any(|b| {
                    b.role == Role::CallArgument
                        && b.point.block == Some(occurrence.site.block)
                        && b.point.statement == Some(occurrence.site.statement)
                        && b.callee
                            .as_deref()
                            .is_some_and(|callee| licensed(callee, b.formal_local))
                })
            {
                continue;
            }
            // The call that supplies a null path's fresh token. It receives no
            // owning argument, so it cannot be returning one of ours.
            if matches!(callee, SourceCallee::Local(_))
                && boundaries.iter().any(|b| {
                    b.role == Role::ReturnReceiver
                        && b.point.block == Some(occurrence.site.block)
                        && b.point.statement == Some(occurrence.site.statement)
                        && takes_no_owning_argument(&boundaries, b)
                })
            {
                continue;
            }
            if !matches!(callee,SourceCallee::ForeignC(name) if name=="free")
                || !sinks.iter().any(|s| {
                    s.endpoint.block == occurrence.site.block
                        && s.endpoint.statement == occurrence.site.statement
                })
            {
                return Err(Error::Unsupported(Site::ForeignCallNotSink));
            }
            continue;
        }
        let pointer = place_type(&occurrence.syntax.destination)?
            .pointer
            .is_some();
        // R330-3: a non-pointer-producing expression is not a token operation
        // when no operand of it is a pointer. `Unrepresented` carries only a
        // description — the branch predicate arrives as `Ne(move _5, const 0)` —
        // so the operand check reads the recorded consumes at this point rather
        // than the string, and fails closed on any place whose type is unknown.
        let touches_pointer = || {
            consumes.iter().filter(|c| at(&c.point)).any(|c| {
                !matches!(
                    place_type(&PlaceSyntax {
                        local: c.local,
                        projection: c.projection.clone(),
                    }),
                    Ok(typed) if typed.pointer.is_none()
                )
            })
        };
        let source = match &occurrence.syntax.expression {
            Expression::Value { operand: value } => operand(value),
            Expression::Cast {
                operand: value,
                cast,
                ..
            } if cast == "PtrToPtr" => operand(value),
            Expression::CopyForDeref { place } => Some(place),
            _ if !pointer && !touches_pointer() => continue,
            _ => return Err(Error::Unsupported(Site::UnsupportedExpression)),
        };
        if !pointer {
            // A POINTER flowing into a non-pointer destination is an escape and
            // stays refused. A non-pointer source — a branch condition such as
            // `pick != 0` — is not a token operation at all, and refusing it
            // would refuse every branching body for computing its own predicate.
            if source
                .is_some_and(|place| place_type(place).is_ok_and(|typed| typed.pointer.is_some()))
            {
                return Err(Error::Unsupported(Site::NonPointerDestinationWithSource));
            }
            continue;
        }
        let source = source.ok_or(Error::Unsupported(Site::SourceOperandMissing))?;
        let covered = equations.iter().any(|e| at(&e.point) && used_equations.contains(&EquationId{construction,ordinal:e.ordinal})
            && e.transfer.as_ref().is_some_and(|t|matches!((&t.source,&t.destination),(Present(s),Present(d))
                if s.local==source.local && s.projection==source.projection && d.local==occurrence.syntax.destination.local && d.projection==occurrence.syntax.destination.projection)));
        let proxy = registrations.iter().any(|r| at(&r.point) && !r.by_reference && r.proxy_local==occurrence.syntax.destination.local
            && matches!(r.source_occurrence,Present(id) if consumes.iter().any(|c|c.ordinal==id && c.point==r.point && c.local==source.local && c.projection==source.projection)));
        if !covered && !proxy {
            // Named rather than folded into `MissingTransfer`, so the store
            // this certificate cannot yet account for stays countable.
            if !occurrence.syntax.destination.projection.is_empty() {
                return Err(Error::Unsupported(Site::FieldStoreDeferred));
            }
            return Err(Error::MissingTransferGap(TransferGap::StoreNotCovered {
                block: occurrence.site.block,
                statement: occurrence.site.statement,
            }));
        }
        if covered {
            let source_consume = one(consumes.iter().filter(|c| {
                at(&c.point) && c.local == source.local && c.projection == source.projection
            }))
            .map_err(|_| Error::MissingTransferGap(TransferGap::ConsumeRecordAbsent))?;
            let destination_consume = one(consumes.iter().filter(|c| {
                at(&c.point)
                    && c.local == occurrence.syntax.destination.local
                    && c.projection == occurrence.syntax.destination.projection
            }))
            .map_err(|_| Error::MissingTransferGap(TransferGap::ConsumeRecordAbsent))?;
            let (Present(source_window), Present(destination_window)) =
                (&source_consume.projected, &destination_consume.projected)
            else {
                return Err(Error::MissingTransferGap(TransferGap::ConsumeWindowAbsent));
            };
            let width = (source_window.use_end - source_window.use_start)
                .min(destination_window.use_end - destination_window.use_start);
            // Native pointer casts deliberately transfer the root only.
            let width = if matches!(occurrence.syntax.expression, Expression::Cast { .. }) {
                width.min(1)
            } else {
                width
            };
            for offset in 0..width {
                let law=one(equations.iter().filter(|e|at(&e.point)
                    && matches!(e.operation.as_str(),"linear"|"equal"|"guarded-copy"|"guarded-move"|"guarded-reader-copy"|"guarded-reader-move")
                    && e.transfer.as_ref().is_some_and(|t|matches!((&t.source,&t.destination),(Present(s),Present(d))
                        if s.consume==source_consume.ordinal && d.consume==destination_consume.ordinal
                            && t.source_use==source_window.use_start+offset
                            && t.destination_use==destination_window.use_start+offset))))
                    .map_err(|_| Error::MissingTransferGap(TransferGap::ComponentLawAbsent))?;
                let transfer = law.transfer.as_ref().unwrap();
                let old_zero = one(equations.iter().filter(|e| {
                    e.point == law.point
                        && e.transfer.as_ref() == Some(transfer)
                        && e.operation == "assume"
                        && e.value == Some(false)
                        && e.variables == [transfer.destination_use]
                }))
                .map_err(|_| {
                    Error::MissingTransferGap(TransferGap::ComponentDestinationNotAssumedZero)
                })?;
                let mut ids = vec![
                    EquationId {
                        construction,
                        ordinal: law.ordinal,
                    },
                    EquationId {
                        construction,
                        ordinal: old_zero.ordinal,
                    },
                ];
                if transfer.by_move && law.operation == "equal" {
                    let moved = one(equations.iter().filter(|e| {
                        e.point == law.point
                            && e.transfer.as_ref() == Some(transfer)
                            && e.operation == "assume"
                            && e.value == Some(false)
                            && e.variables == [transfer.source_def]
                    }))
                    .map_err(|_| {
                        Error::MissingTransferGap(TransferGap::ComponentSourceNotAssumedZero)
                    })?;
                    ids.push(EquationId {
                        construction,
                        ordinal: moved.ordinal,
                    });
                }
                proof.actions.push(Action {
                    block: occurrence.site.block,
                    statement: occurrence.site.statement,
                    kind: "component-law".into(),
                    equations: ids,
                    zero_requirements: vec![],
                });
            }
        }
    }
    let zero_actions = super::fold_zero::certify(facts, &proof, order, &null_fields)?;
    proof.actions.extend(zero_actions);
    proof.required_guards = required_guards.into_iter().collect();
    let zeros = terminals
        .iter()
        .filter(|t| t.local != 0)
        .flat_map(|t| match &t.values {
            Present(values) => values.iter().map(|v| node(v.var)).collect(),
            _ => vec![],
        })
        .collect();
    proof.actions.push(Action {
        block: returned.point.block.ok_or(Error::Coverage(line!()))?,
        statement: returned.point.statement.ok_or(Error::Coverage(line!()))?,
        kind: "return-subtree".into(),
        equations: vec![],
        zero_requirements: zeros,
    });
    if proof
        .actions
        .iter()
        .flat_map(|action| &action.zero_requirements)
        .any(|node| demanded.contains(node))
    {
        return Err(Error::CompetingDisposition);
    }
    // A taken child's latent descendants remain inside that child's token.
    // This record creates neither extra SSA values nor allocation endpoints.
    proof.used_fields.sort();
    proof.used_fields.dedup();
    proof
        .actions
        .sort_by_key(|a| (*order.get(&a.block).unwrap(), a.statement, a.kind.clone()));
    Ok(proof)
}
