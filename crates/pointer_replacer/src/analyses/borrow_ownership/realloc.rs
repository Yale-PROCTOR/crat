//! Source-derived realloc outcomes shared by ownership and retirement replay.
//!
//! Outcomes are feasible source alternatives, never solver-selected Boolean
//! branches. Direct result tests and P0-backed uses carry separate evidence.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Location, Operand, RETURN_PLACE, Rvalue,
        StatementKind, TerminatorKind, UnOp,
    },
    ty::TyCtxt,
};

use super::{
    export::PlaceKey,
    source_events::{
        SourcePhase, addressed_locals, null_entries, operand_is_null, transfer_statement,
    },
};
use crate::{
    analyses::mir::{CallKind, TerminatorExt},
    utils::rustc::RustProgram,
};

mod field_result;
mod use_evidence;

#[cfg(test)]
mod coverage_tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ReallocOutcome {
    Success,
    Failure,
}

/// The same source-call coordinates carried by `SourceEventKey`. An outcome
/// expands this identity; it does not create a second source call or an epoch.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ReallocSiteKey {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) phase: SourcePhase,
}

/// Declaration class must come from compiler identity, never just its spelling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReallocCalleeIdentity {
    ForeignC(String),
    LocalFunction(String),
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OldInput {
    KnownNull,
    MayBeNonNull,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReallocSize {
    Nonzero,
    Zero,
    /// The primitive's explicit byte-count contract applies to a dynamic
    /// argument. This is neither an element-size fact nor a nonzero proof.
    ByteCount,
    /// There is no established byte-count/element-size contract.
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ZeroSizeFeasibility {
    Possible,
    /// A source guard excludes zero on every route reaching this call.
    ExcludedBySourceGuard(Location),
}

/// SameAsOld describes a hypothetical successful outcome. A source comparison
/// between result and old pointer cannot establish this property or success.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SuccessAddress {
    Unknown,
    SameAsOld,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResultTransport {
    pub(crate) location: Location,
    pub(crate) source: Local,
    pub(crate) destination: Local,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocBranch {
    /// Exact bare MIR arg0 operand, often a compiler call-argument proxy.
    /// Ownership integration must normalize it using its own consume metadata.
    pub(crate) old: Option<Local>,
    /// Original call destination, never the last alias used by the null test.
    pub(crate) result: Local,
    /// The SwitchInt selecting the two source outcomes.
    pub(crate) test: Location,
    pub(crate) success: BasicBlock,
    pub(crate) failure: BasicBlock,
    pub(crate) transports: Vec<ResultTransport>,
}

/// A source operation that excludes a null result on P0-admitted executions.
/// A dereference merely present on one optional path is not such a witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReallocUseWitness {
    DirectDeref {
        location: Location,
        place: PlaceKey,
        /// Actual access size; zero does not establish usable allocated bytes.
        access_bytes: u64,
    },
    LocalCall {
        location: Location,
        callee: String,
        /// Zero-based source call argument position.
        argument: usize,
        callee_deref: Location,
        access_bytes: u64,
    },
}

/// Original operands of an unbranched source continuation. Projected places
/// remain present even when they have no bare-local ownership representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocContinuation {
    /// Exact raw call operand; ownership normalization is a separate operation.
    pub(crate) old: Option<Local>,
    pub(crate) old_place: Option<PlaceKey>,
    /// Original realloc destination, never the final tested/dereferenced alias.
    pub(crate) result: Option<Local>,
    pub(crate) result_place: PlaceKey,
    pub(crate) normal: BasicBlock,
    pub(crate) transports: Vec<ResultTransport>,
    /// Present for SuccessImplied; absent for Unobserved.
    pub(crate) witness: Option<ReallocUseWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FieldResultTransport {
    pub(crate) location: Location,
    pub(crate) source: PlaceKey,
    pub(crate) destination: PlaceKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReallocResultTestReceipt {
    FallbackBothOutcomes,
}
impl ReallocResultTestReceipt {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::FallbackBothOutcomes => "realloc-result-test:fallback-both-outcomes",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReallocResult {
    DirectBranch(ReallocBranch),
    /// R219 B: an unconditional dereferencing use excludes failure under P0.
    SuccessImplied(ReallocContinuation),
    /// R219 B: no test/use selects an outcome; both source cases remain.
    Unobserved(ReallocContinuation),
    /// Source test is known, while field storage uses the conservative call
    /// boundary representation rather than invented bare-local SSA versions.
    FieldBranch {
        branch: ReallocBranch,
        continuation: ReallocContinuation,
        field_transports: Vec<FieldResultTransport>,
    },
    /// R243: unclassified result control keeps both outcomes and a source-site receipt.
    FallbackBothOutcomes(ReallocContinuation),
    Discarded,
    UnresolvedTest,
}

impl ReallocResult {
    pub(crate) fn continuation(&self) -> Option<&ReallocContinuation> {
        match self {
            Self::SuccessImplied(row)
            | Self::Unobserved(row)
            | Self::FallbackBothOutcomes(row)
            | Self::FieldBranch {
                continuation: row, ..
            } => Some(row),
            _ => None,
        }
    }

    pub(crate) fn result_test_receipt(&self) -> Option<ReallocResultTestReceipt> {
        matches!(self, Self::FallbackBothOutcomes(_) | Self::UnresolvedTest)
            .then_some(ReallocResultTestReceipt::FallbackBothOutcomes)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocSite {
    pub(crate) key: ReallocSiteKey,
    pub(crate) callee: ReallocCalleeIdentity,
    pub(crate) old_input: OldInput,
    pub(crate) size: ReallocSize,
    /// ByteCount requires explicit zero feasibility. Static sizes carry their
    /// own classification; None is never evidence that a dynamic size is > 0.
    pub(crate) zero_size: Option<ZeroSizeFeasibility>,
    pub(crate) result: ReallocResult,
    pub(crate) success_address: SuccessAddress,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReallocUnsupported {
    NotForeignCRealloc,
    ZeroSize,
    UnknownSize,
    DiscardedResult,
    UnresolvedResultTest,
}

/// These are responsibility and lifecycle effects on the old generation, if
/// present. A possibly null input must not fabricate a generation to retire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OldResponsibility {
    RetireIfPresent,
    PreserveIfPresent,
    /// The loss law removes the source claim. This effect alone makes no
    /// physical retirement or contents claim; those facts remain separate.
    LoseClaimIfPresent,
    Absent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ResultResponsibility {
    /// A fresh generation and responsibility, even at the same numeric address.
    FreshGeneration,
    /// Null result, with no new allocation responsibility.
    None,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ContentsRelation {
    /// The primitive preserves its required prefix; this is no extent proof.
    RequiredPrefixPreserved,
    OldContentsUnchanged,
    /// A possible zero-size case has target-dependent retirement/content
    /// behavior. In particular, unchanged old bytes are not asserted.
    TargetDependentZeroSize,
    NoOldObject,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReallocRetirementAvailability {
    Unclassified,
    None,
    WholeOldGeneration,
    MayRetireOnZero,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ReallocCase {
    pub(crate) outcome: ReallocOutcome,
    pub(crate) old: OldResponsibility,
    pub(crate) result: ResultResponsibility,
    pub(crate) contents: ContentsRelation,
}

pub(crate) fn zero_size_possible(site: &ReallocSite) -> bool {
    site.size == ReallocSize::Zero
        || (site.size == ReallocSize::ByteCount
            && !matches!(
                site.zero_size,
                Some(ZeroSizeFeasibility::ExcludedBySourceGuard(_))
            ))
}

/// Claim loss and physical retirement are independent facts, particularly for
/// a dynamic byte count whose zero-size target behavior is not resolved.
pub(crate) fn retirement_availability(
    site: &ReallocSite,
    case: &ReallocCase,
) -> ReallocRetirementAvailability {
    if site.old_input == OldInput::KnownNull || case.old == OldResponsibility::Absent {
        return ReallocRetirementAvailability::None;
    }
    match (case.outcome, case.old) {
        (ReallocOutcome::Success, OldResponsibility::RetireIfPresent) => {
            ReallocRetirementAvailability::WholeOldGeneration
        }
        (
            ReallocOutcome::Failure,
            OldResponsibility::PreserveIfPresent | OldResponsibility::LoseClaimIfPresent,
        ) if site.size != ReallocSize::Unknown => {
            if zero_size_possible(site) {
                ReallocRetirementAvailability::MayRetireOnZero
            } else {
                ReallocRetirementAvailability::None
            }
        }
        _ => ReallocRetirementAvailability::Unclassified,
    }
}

fn requested_size(operand: &Operand<'_>, tcx: TyCtxt<'_>) -> ReallocSize {
    let Operand::Constant(value) = operand else { return ReallocSize::ByteCount };
    let scalar = value.const_.try_to_scalar().or_else(|| {
        if let rustc_middle::mir::Const::Unevaluated(value, _) = &value.const_
            && value.promoted.is_none()
            && let Ok(rustc_middle::mir::ConstValue::Scalar(scalar)) =
                tcx.const_eval_poly(value.def)
        {
            return Some(scalar);
        }
        None
    });
    match scalar.and_then(|scalar| scalar.try_to_scalar_int().ok()) {
        Some(value) if value.to_bits(value.size()) == 0 => ReallocSize::Zero,
        Some(_) => ReallocSize::Nonzero,
        None => ReallocSize::ByteCount,
    }
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    operand.place().and_then(|place| place.as_local())
}

/// Only compiler-resolved core pointer observations are transparent calls.
fn is_pointer_null_test(callee: &CallKind, tcx: TyCtxt<'_>) -> bool {
    matches!(callee, CallKind::RustLib(did)
        if tcx.item_name(*did).as_str() == "is_null"
            && tcx.crate_name(did.krate).as_str() == "core"
            && tcx.def_path_str(*did).contains("::ptr::"))
}

fn null_comparison(
    value: &Rvalue<'_>,
    aliases: &BTreeSet<Local>,
    nulls: &[bool],
    tcx: TyCtxt<'_>,
) -> Option<bool> {
    let Rvalue::BinaryOp(operator @ (BinOp::Eq | BinOp::Ne), operands) = value else {
        return None;
    };
    let (left, right) = &**operands;
    let left_is_result = operand_local(left).is_some_and(|local| aliases.contains(&local));
    let right_is_result = operand_local(right).is_some_and(|local| aliases.contains(&local));
    ((left_is_result && operand_is_null(right, nulls, tcx))
        || (right_is_result && operand_is_null(left, nulls, tcx)))
    .then_some(*operator == BinOp::Eq)
}

fn result_branch<'tcx>(
    body: &Body<'tcx>,
    call_block: BasicBlock,
    old: Option<Local>,
    result: Local,
    first: BasicBlock,
    entries: &[Option<Vec<bool>>],
    addressed: &BTreeSet<Local>,
    tcx: TyCtxt<'tcx>,
) -> ReallocResult {
    // A predecessor join or revisit before the null test loses the exact result
    // correlation. No arbitrary iteration cap or source-CFG rewrite is needed.
    let mut predecessors = vec![BTreeSet::new(); body.basic_blocks.len()];
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for successor in data.terminator().successors() {
            predecessors[successor.as_usize()].insert(block);
        }
    }
    let mut visited = BTreeSet::from([call_block]);
    let mut previous = call_block;
    let mut block = first;
    let mut aliases = BTreeSet::from([result]);
    let mut predicates = BTreeMap::new();
    let mut transports = Vec::new();
    let mut observed = false;

    loop {
        if !visited.insert(block) || predecessors[block.as_usize()] != BTreeSet::from([previous]) {
            return ReallocResult::UnresolvedTest;
        }
        let data = &body.basic_blocks[block];
        let mut nulls = entries[block.as_usize()]
            .clone()
            .unwrap_or_else(|| vec![false; body.local_decls.len()]);
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            match &statement.kind {
                StatementKind::Assign(box (destination, value)) => {
                    let Some(destination) = destination.as_local() else {
                        return ReallocResult::UnresolvedTest;
                    };
                    if addressed.contains(&destination) || Some(destination) == old {
                        return ReallocResult::UnresolvedTest;
                    }
                    let copy = match value {
                        Rvalue::Use(operand) => operand_local(operand),
                        Rvalue::Cast(CastKind::PtrToPtr, operand, _)
                            if body.local_decls[destination].ty.is_raw_ptr() =>
                        {
                            operand_local(operand)
                                .filter(|local| body.local_decls[*local].ty.is_raw_ptr())
                        }
                        _ => None,
                    };
                    if let Some(source) = copy.filter(|source| aliases.contains(source)) {
                        if !body.local_decls[destination].ty.is_raw_ptr()
                            || aliases.contains(&destination)
                            || predicates.contains_key(&destination)
                        {
                            return ReallocResult::UnresolvedTest;
                        }
                        aliases.insert(destination);
                        transports.push(ResultTransport {
                            location,
                            source,
                            destination,
                        });
                    } else if let Some(null_when_true) =
                        null_comparison(value, &aliases, &nulls, tcx)
                    {
                        if observed || aliases.contains(&destination) {
                            return ReallocResult::UnresolvedTest;
                        }
                        predicates.insert(destination, null_when_true);
                        observed = true;
                    } else if let Some(null_when_true) = match value {
                        Rvalue::Use(operand) => {
                            operand_local(operand).and_then(|local| predicates.get(&local).copied())
                        }
                        Rvalue::UnaryOp(UnOp::Not, operand) => operand_local(operand)
                            .and_then(|local| predicates.get(&local).map(|value| !*value)),
                        _ => None,
                    } {
                        if aliases.contains(&destination) {
                            return ReallocResult::UnresolvedTest;
                        }
                        predicates.insert(destination, null_when_true);
                    } else {
                        // Permit only construction of an independent null value
                        // needed by an explicit `result == null` observation.
                        if aliases.contains(&destination) || predicates.contains_key(&destination) {
                            return ReallocResult::UnresolvedTest;
                        }
                        if destination == RETURN_PLACE
                            && body.local_decls[destination].ty.is_unit()
                            && matches!(value, Rvalue::Use(Operand::Constant(_)))
                        {
                            continue;
                        }
                        transfer_statement(&statement.kind, &mut nulls, addressed, tcx);
                        if !nulls[destination.as_usize()] {
                            return ReallocResult::UnresolvedTest;
                        }
                        continue;
                    }
                }
                StatementKind::StorageDead(local) => {
                    aliases.remove(local);
                    predicates.remove(local);
                }
                StatementKind::StorageLive(_)
                | StatementKind::Nop
                | StatementKind::ConstEvalCounter
                | StatementKind::Coverage(_) => {}
                _ => return ReallocResult::UnresolvedTest,
            }
            transfer_statement(&statement.kind, &mut nulls, addressed, tcx);
        }

        let terminator = data.terminator();
        let next = match &terminator.kind {
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::Call {
                target: Some(target),
                ..
            } => {
                let call = terminator.as_call(tcx).expect("call terminator");
                let Some(destination) = call.destination.as_local() else {
                    return ReallocResult::UnresolvedTest;
                };
                if addressed.contains(&destination)
                    || aliases.contains(&destination)
                    || predicates.contains_key(&destination)
                    || Some(destination) == old
                {
                    return ReallocResult::UnresolvedTest;
                }
                if is_pointer_null_test(&call.func, tcx)
                    && call.args.len() == 1
                    && operand_local(&call.args[0].node)
                        .is_some_and(|local| aliases.contains(&local))
                {
                    if observed {
                        return ReallocResult::UnresolvedTest;
                    }
                    predicates.insert(destination, true);
                    observed = true;
                } else if !(call.args.is_empty()
                    && entries[target.as_usize()]
                        .as_ref()
                        .is_some_and(|state| state[destination.as_usize()]))
                {
                    // The shared null producer marks a call result null only
                    // for its exact core null constructor. Do not duplicate or
                    // weaken that classifier here.
                    return ReallocResult::UnresolvedTest;
                }
                *target
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let Some(null_when_true) =
                    operand_local(discr).and_then(|local| predicates.get(&local).copied())
                else {
                    return ReallocResult::UnresolvedTest;
                };
                let target_for = |value| {
                    targets
                        .iter()
                        .find_map(|(candidate, target)| (candidate == value).then_some(target))
                        .unwrap_or_else(|| targets.otherwise())
                };
                let failure = target_for(u128::from(null_when_true));
                let success = target_for(u128::from(!null_when_true));
                if success == failure || visited.contains(&success) || visited.contains(&failure) {
                    return ReallocResult::UnresolvedTest;
                }
                return ReallocResult::DirectBranch(ReallocBranch {
                    old,
                    result,
                    test: Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    success,
                    failure,
                    transports,
                });
            }
            TerminatorKind::Return if !observed && transports.is_empty() => {
                return ReallocResult::Discarded;
            }
            _ => return ReallocResult::UnresolvedTest,
        };
        previous = block;
        block = next;
    }
}

pub(crate) fn collect_sites(program: &RustProgram<'_>) -> Vec<ReallocSite> {
    let tcx = program.tcx;
    let mut sites = Vec::new();
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let addressed = addressed_locals(&body);
        let entries = null_entries(&body, &addressed, tcx);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let terminator = data.terminator();
            let Some(call) = terminator.as_call(tcx) else { continue };
            if !matches!(call.func, CallKind::LibC(name) if name.as_str() == "realloc") {
                continue;
            }
            let mut nulls = entries[block.as_usize()]
                .clone()
                .unwrap_or_else(|| vec![false; body.local_decls.len()]);
            for statement in &data.statements {
                transfer_statement(&statement.kind, &mut nulls, &addressed, tcx);
            }
            let old_input = if call
                .args
                .first()
                .is_some_and(|argument| operand_is_null(&argument.node, &nulls, tcx))
            {
                OldInput::KnownNull
            } else {
                OldInput::MayBeNonNull
            };
            let old = call
                .args
                .first()
                .and_then(|argument| operand_local(&argument.node));
            let size = call
                .args
                .get(1)
                .filter(|argument| argument.node.ty(&*body, tcx).is_integral())
                .map(|argument| requested_size(&argument.node, tcx))
                .unwrap_or(ReallocSize::Unknown);
            let zero_size = (size == ReallocSize::ByteCount).then(|| {
                call.args
                    .get(1)
                    .and_then(|argument| {
                        use_evidence::nonzero_guard(&body, block, &argument.node, tcx)
                    })
                    .map(ZeroSizeFeasibility::ExcludedBySourceGuard)
                    .unwrap_or(ZeroSizeFeasibility::Possible)
            });
            let mut result = match (&terminator.kind, call.destination.as_local()) {
                (
                    TerminatorKind::Call {
                        target: Some(target),
                        ..
                    },
                    Some(result),
                ) if call.args.len() == 2
                    && (old.is_some() || old_input == OldInput::KnownNull)
                    && !addressed.contains(&result) =>
                {
                    result_branch(
                        &body, block, old, result, *target, &entries, &addressed, tcx,
                    )
                }
                _ => ReallocResult::UnresolvedTest,
            };
            if !matches!(result, ReallocResult::DirectBranch(_))
                && let TerminatorKind::Call {
                    target: Some(normal),
                    ..
                } = &terminator.kind
                && call.args.len() == 2
            {
                let old_place = call.args.first().and_then(|argument| argument.node.place());
                result = if let Some(result_local) = call.destination.as_local()
                    && let Some((branch, field_transports)) = field_result::branch(
                        &body,
                        block,
                        old,
                        result_local,
                        *normal,
                        &entries,
                        &addressed,
                        tcx,
                    ) {
                    ReallocResult::FieldBranch {
                        branch,
                        continuation: ReallocContinuation {
                            old,
                            old_place: old_place.map(PlaceKey::from_place),
                            result: Some(result_local),
                            result_place: PlaceKey::from_place(call.destination),
                            normal: *normal,
                            transports: Vec::new(),
                            witness: None,
                        },
                        field_transports,
                    }
                } else {
                    use_evidence::continuation(
                        program,
                        &body,
                        block,
                        *normal,
                        old_place,
                        call.destination,
                    )
                };
            }
            sites.push(ReallocSite {
                key: ReallocSiteKey {
                    function: tcx.def_path_str(function.to_def_id()),
                    block: block.as_u32(),
                    statement: data.statements.len(),
                    phase: SourcePhase::Call,
                },
                callee: ReallocCalleeIdentity::ForeignC("realloc".to_owned()),
                old_input,
                size,
                zero_size,
                result,
                success_address: SuccessAddress::Unknown,
            });
        }
    }
    sites.sort_by(|left, right| left.key.cmp(&right.key));
    sites
}

pub(crate) fn classify(site: &ReallocSite) -> Result<Vec<ReallocCase>, ReallocUnsupported> {
    if !matches!(&site.callee, ReallocCalleeIdentity::ForeignC(name) if name == "realloc") {
        return Err(ReallocUnsupported::NotForeignCRealloc);
    }
    match site.size {
        ReallocSize::Zero => return Err(ReallocUnsupported::ZeroSize),
        ReallocSize::Unknown => return Err(ReallocUnsupported::UnknownSize),
        ReallocSize::Nonzero | ReallocSize::ByteCount => {}
    }
    let mut success_only = false;
    let mut lose_failure_claim = false;
    match &site.result {
        ReallocResult::Discarded => return Err(ReallocUnsupported::DiscardedResult),
        ReallocResult::UnresolvedTest => {
            lose_failure_claim = true;
        }
        ReallocResult::FallbackBothOutcomes(_) | ReallocResult::FieldBranch { .. } => {
            lose_failure_claim = true;
        }
        ReallocResult::SuccessImplied(continuation) => {
            let access_bytes = match &continuation.witness {
                Some(
                    ReallocUseWitness::DirectDeref { access_bytes, .. }
                    | ReallocUseWitness::LocalCall { access_bytes, .. },
                ) => *access_bytes,
                None => 0,
            };
            if access_bytes == 0
                || (continuation.old_place.is_none() && site.old_input != OldInput::KnownNull)
            {
                return Err(ReallocUnsupported::UnresolvedResultTest);
            }
            // P0 admits the witnessed positive-sized access only when this
            // allocation supplied usable bytes. Nonnull alone does not do so.
            success_only = true;
        }
        ReallocResult::Unobserved(continuation) => {
            if continuation.witness.is_some()
                || (continuation.old_place.is_none() && site.old_input != OldInput::KnownNull)
            {
                return Err(ReallocUnsupported::UnresolvedResultTest);
            }
            lose_failure_claim = true;
        }
        ReallocResult::DirectBranch(branch)
            if branch.success == branch.failure
                || (branch.old.is_none() && site.old_input != OldInput::KnownNull) =>
        {
            return Err(ReallocUnsupported::UnresolvedResultTest);
        }
        ReallocResult::DirectBranch(_) => {
            if zero_size_possible(site) {
                return Err(ReallocUnsupported::ZeroSize);
            }
        }
    }
    let old_present = site.old_input != OldInput::KnownNull;
    let mut cases = vec![ReallocCase {
        outcome: ReallocOutcome::Success,
        old: if old_present {
            OldResponsibility::RetireIfPresent
        } else {
            OldResponsibility::Absent
        },
        result: ResultResponsibility::FreshGeneration,
        contents: if old_present {
            ContentsRelation::RequiredPrefixPreserved
        } else {
            ContentsRelation::NoOldObject
        },
    }];
    if !success_only {
        cases.push(ReallocCase {
            outcome: ReallocOutcome::Failure,
            old: if old_present && lose_failure_claim {
                OldResponsibility::LoseClaimIfPresent
            } else if old_present {
                OldResponsibility::PreserveIfPresent
            } else {
                OldResponsibility::Absent
            },
            result: ResultResponsibility::None,
            contents: if old_present && zero_size_possible(site) {
                ContentsRelation::TargetDependentZeroSize
            } else if old_present {
                ContentsRelation::OldContentsUnchanged
            } else {
                ContentsRelation::NoOldObject
            },
        });
    }
    Ok(cases)
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::*;

    const FOREIGN: &str =
        "unsafe extern \"C\" { fn realloc(p: *mut u8, n: usize) -> *mut u8; fn free(p: *mut u8); }";

    fn sites(code: &str) -> Vec<ReallocSite> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
            collect_sites(&RustProgram {
                tcx,
                functions,
                structs,
            })
        })
        .unwrap_or_else(|error| error.raise())
    }

    fn one_site(body: &str) -> ReallocSite {
        let mut sites = sites(&format!("{FOREIGN} {body}"));
        assert_eq!(
            sites.len(),
            1,
            "one source realloc call must be inventoried"
        );
        sites.pop().unwrap()
    }

    fn assert_result_test_fallback(site: &ReallocSite) {
        assert!(matches!(
            site.result,
            ReallocResult::FallbackBothOutcomes(_)
        ));
        assert_eq!(
            site.result.result_test_receipt(),
            Some(ReallocResultTestReceipt::FallbackBothOutcomes)
        );
        let cases = classify(site).expect("R243 keeps both source outcomes");
        assert_eq!(cases.len(), 2);
        assert!(
            cases
                .iter()
                .any(|case| case.outcome == ReallocOutcome::Success
                    && case.old == OldResponsibility::RetireIfPresent
                    && case.result == ResultResponsibility::FreshGeneration)
        );
        assert!(
            cases
                .iter()
                .any(|case| case.outcome == ReallocOutcome::Failure
                    && case.old == OldResponsibility::LoseClaimIfPresent
                    && case.result == ResultResponsibility::None)
        );
    }

    fn synthetic_site() -> ReallocSite {
        ReallocSite {
            key: ReallocSiteKey {
                function: "fixture".to_owned(),
                block: 0,
                statement: 0,
                phase: SourcePhase::Call,
            },
            callee: ReallocCalleeIdentity::ForeignC("realloc".to_owned()),
            old_input: OldInput::MayBeNonNull,
            size: ReallocSize::Nonzero,
            zero_size: None,
            result: ReallocResult::DirectBranch(ReallocBranch {
                old: Some(Local::from_u32(1)),
                result: Local::from_u32(2),
                test: Location {
                    block: BasicBlock::from_u32(1),
                    statement_index: 0,
                },
                success: BasicBlock::from_u32(2),
                failure: BasicBlock::from_u32(3),
                transports: Vec::new(),
            }),
            success_address: SuccessAddress::Unknown,
        }
    }

    fn nonzero_cases() -> Vec<ReallocCase> {
        vec![
            ReallocCase {
                outcome: ReallocOutcome::Success,
                old: OldResponsibility::RetireIfPresent,
                result: ResultResponsibility::FreshGeneration,
                contents: ContentsRelation::RequiredPrefixPreserved,
            },
            ReallocCase {
                outcome: ReallocOutcome::Failure,
                old: OldResponsibility::PreserveIfPresent,
                result: ResultResponsibility::None,
                contents: ContentsRelation::OldContentsUnchanged,
            },
        ]
    }

    #[test]
    fn e5_r_fail_source_branch_preserves_old_contents_and_responsibility() {
        let site = one_site(
            "pub unsafe fn failure(p: *mut u8) -> u8 { let q = realloc(p, 16); if q.is_null() { let value = *p; free(p); value } else { free(q); 0 } }",
        );
        assert_eq!(site.key.function, "failure");
        assert_eq!(site.key.phase, SourcePhase::Call);
        assert_eq!(site.size, ReallocSize::Nonzero);
        let ReallocResult::DirectBranch(branch) = &site.result else {
            panic!("the source null test must produce a direct branch plan");
        };
        assert_ne!(branch.success, branch.failure);
        assert!(branch.old.is_some());
        assert_eq!(classify(&site), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r_success_source_branch_transfers_to_fresh_result() {
        let site = one_site(
            "pub unsafe fn success(mut p: *mut u8) { let q = realloc(p, 16); if q.is_null() { free(p); } else { p = q; free(p); } }",
        );
        assert_eq!(classify(&site), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r_same_address_success_still_has_a_fresh_generation() {
        let mut site = synthetic_site();
        site.success_address = SuccessAddress::SameAsOld;
        assert_eq!(
            classify(&site),
            Ok(nonzero_cases()),
            "equal addresses do not merge generations or discard the failure case"
        );
    }

    #[test]
    fn e5_r_source_address_comparison_does_not_choose_success() {
        let site = one_site(
            "pub unsafe fn same_address(p: *mut u8) -> bool { let q = realloc(p, 16); if q.is_null() { free(p); false } else { let same = q == p; free(q); same } }",
        );
        assert_eq!(site.success_address, SuccessAddress::Unknown);
        assert_eq!(classify(&site), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r_nonzero_classifier_keeps_both_feasible_outcomes() {
        assert_eq!(classify(&synthetic_site()), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r_known_null_old_has_no_old_responsibility_or_retirement() {
        let site = one_site(
            "pub unsafe fn null_old() { let q = realloc(0 as *mut u8, 16); if q.is_null() { return; } free(q); }",
        );
        assert_eq!(site.old_input, OldInput::KnownNull);
        assert_eq!(
            classify(&site),
            Ok(vec![
                ReallocCase {
                    outcome: ReallocOutcome::Success,
                    old: OldResponsibility::Absent,
                    result: ResultResponsibility::FreshGeneration,
                    contents: ContentsRelation::NoOldObject,
                },
                ReallocCase {
                    outcome: ReallocOutcome::Failure,
                    old: OldResponsibility::Absent,
                    result: ResultResponsibility::None,
                    contents: ContentsRelation::NoOldObject,
                },
            ])
        );
    }

    #[test]
    fn e5_r_source_result_copy_and_cast_keep_the_null_test_identity() {
        let site = one_site(
            "pub unsafe fn transport(p: *mut u8) { let q = realloc(p, 16); let copied = q; let tested = copied as *mut i8; if tested.is_null() { free(p); } else { free(q); } }",
        );
        let ReallocResult::DirectBranch(branch) = &site.result else {
            panic!("a value-preserving result transport must retain its null test");
        };
        assert!(
            !branch.transports.is_empty(),
            "transport sites need evidence"
        );
        assert_eq!(classify(&site), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r_exact_foreign_identity_is_required_even_for_realloc_spelling() {
        let mut local = synthetic_site();
        local.callee = ReallocCalleeIdentity::LocalFunction("realloc".to_owned());
        assert_eq!(
            classify(&local),
            Err(ReallocUnsupported::NotForeignCRealloc)
        );
        let mut other_foreign = synthetic_site();
        other_foreign.callee = ReallocCalleeIdentity::ForeignC("malloc".to_owned());
        assert_eq!(
            classify(&other_foreign),
            Err(ReallocUnsupported::NotForeignCRealloc)
        );
        let mut indirect = synthetic_site();
        indirect.callee = ReallocCalleeIdentity::Other;
        assert_eq!(
            classify(&indirect),
            Err(ReallocUnsupported::NotForeignCRealloc)
        );
    }

    #[test]
    fn e5_r_source_local_realloc_name_is_not_a_foreign_primitive() {
        let sites = sites(
            "unsafe fn realloc(p: *mut u8, _n: usize) -> *mut u8 { p } pub unsafe fn local(p: *mut u8) -> *mut u8 { realloc(p, 16) }",
        );
        assert!(sites.is_empty(), "local wrappers require body semantics");
    }

    #[test]
    fn e5_r_zero_size_is_typed_unsupported_not_nonzero_failure() {
        let site = one_site(
            "pub unsafe fn zero_size(p: *mut u8) -> bool { let q = realloc(p, 0); q.is_null() }",
        );
        assert_eq!(site.size, ReallocSize::Zero);
        assert_eq!(classify(&site), Err(ReallocUnsupported::ZeroSize));
    }

    #[test]
    fn e5_r_dynamic_bytes_with_opaque_result_keep_result_hold() {
        let site = one_site(
            "pub unsafe fn unknown_size(p: *mut u8, n: usize) -> bool { let q = realloc(p, n); q.is_null() }",
        );
        // R219: the byte contract is present, while a returned null predicate
        // still supplies no direct source-outcome control edge.
        assert_eq!(site.size, ReallocSize::ByteCount);
        assert_result_test_fallback(&site);
    }

    #[test]
    fn e5_r_discarded_result_is_not_an_unconditional_old_sink() {
        let site = one_site("pub unsafe fn discarded(p: *mut u8) { realloc(p, 16); }");
        assert!(matches!(site.result, ReallocResult::Unobserved(_)));
        let cases = classify(&site).expect("R219 unobserved outcomes");
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0], nonzero_cases()[0]);
        assert_eq!(cases[1].outcome, ReallocOutcome::Failure);
        assert_eq!(cases[1].old, OldResponsibility::LoseClaimIfPresent);
        assert_eq!(cases[1].result, ResultResponsibility::None);
        assert_eq!(
            retirement_availability(&site, &cases[1]),
            ReallocRetirementAvailability::None
        );
    }

    #[test]
    fn e5_r_unresolved_result_test_is_typed_unsupported() {
        let site = one_site(
            "pub unsafe fn unresolved(p: *mut u8) -> bool { let q = realloc(p, 16); q == p }",
        );
        // R243 supersedes the historical unsupported-result expectation.
        assert_result_test_fallback(&site);
    }

    fn success_continuation(site: &ReallocSite) -> &ReallocContinuation {
        let ReallocResult::SuccessImplied(continuation) = &site.result else {
            panic!(
                "R219 B requires source-backed success evidence: {:?}",
                site.result
            );
        };
        assert!(
            continuation.witness.is_some(),
            "P0 implication needs a use witness"
        );
        continuation
    }

    #[test]
    fn e5_r219_untested_unconditional_dereference_implies_success_under_p0() {
        let site = one_site(
            "pub unsafe fn dereferenced(p: *mut u8) -> u8 { let q = realloc(p, 16); let value = *q; free(q); value }",
        );
        let continuation = success_continuation(&site);
        assert!(matches!(
            continuation.witness,
            Some(ReallocUseWitness::DirectDeref { .. })
        ));
        assert!(
            continuation.old_place.is_some(),
            "preserve the exact old operand"
        );
        assert_eq!(continuation.result, Some(continuation.result_place.local));
        assert_eq!(classify(&site), Ok(vec![nonzero_cases()[0]]));
    }

    #[test]
    fn e5_r219_result_transport_preserves_original_result_and_deref_evidence() {
        let site = one_site(
            "pub unsafe fn transported(p: *mut u8) -> i8 { let q = realloc(p, 16); let copied = q; let view = copied as *mut i8; let value = *view; free(q); value }",
        );
        let continuation = success_continuation(&site);
        assert!(
            continuation
                .transports
                .iter()
                .any(|transport| { transport.source == continuation.result_place.local }),
            "the source allocation destination must remain the transport root"
        );
        let Some(ReallocUseWitness::DirectDeref { place, .. }) = &continuation.witness else {
            panic!("the transported dereference requires its exact place witness");
        };
        assert!(!place.proj.is_empty());
        assert_eq!(classify(&site), Ok(vec![nonzero_cases()[0]]));
    }

    #[test]
    fn e5_r219_unconditional_local_dereferencing_call_implies_success() {
        let site = one_site(
            "unsafe fn read_byte(value: *mut u8) -> u8 { *value } pub unsafe fn passed_to_reader(p: *mut u8) -> u8 { let q = realloc(p, 16); let value = read_byte(q); free(q); value }",
        );
        let continuation = success_continuation(&site);
        let Some(ReallocUseWitness::LocalCall {
            callee, argument, ..
        }) = &continuation.witness
        else {
            panic!("a local call must carry callee/argument and callee-dereference evidence");
        };
        assert_eq!(callee, "read_byte");
        assert_eq!(*argument, 0);
        assert_eq!(classify(&site), Ok(vec![nonzero_cases()[0]]));
    }

    #[test]
    fn e5_r219_unobserved_result_keeps_both_cases_and_failure_loses_only_claim() {
        let site = one_site("pub unsafe fn unobserved(p: *mut u8) { realloc(p, 16); }");
        let ReallocResult::Unobserved(continuation) = &site.result else {
            panic!("no test/use must preserve both outcomes, including the source leak");
        };
        assert!(continuation.witness.is_none());
        assert!(continuation.old_place.is_some());
        assert_eq!(
            classify(&site),
            Ok(vec![
                nonzero_cases()[0],
                ReallocCase {
                    outcome: ReallocOutcome::Failure,
                    old: OldResponsibility::LoseClaimIfPresent,
                    result: ResultResponsibility::None,
                    contents: ContentsRelation::OldContentsUnchanged,
                },
            ])
        );
    }

    #[test]
    fn e5_r219_unobserved_null_old_has_no_claim_to_lose_or_retire() {
        let site = one_site("pub unsafe fn unobserved_null() { realloc(0 as *mut u8, 16); }");
        assert_eq!(site.old_input, OldInput::KnownNull);
        assert!(matches!(site.result, ReallocResult::Unobserved(_)));
        assert_eq!(
            classify(&site),
            Ok(vec![
                ReallocCase {
                    outcome: ReallocOutcome::Success,
                    old: OldResponsibility::Absent,
                    result: ResultResponsibility::FreshGeneration,
                    contents: ContentsRelation::NoOldObject,
                },
                ReallocCase {
                    outcome: ReallocOutcome::Failure,
                    old: OldResponsibility::Absent,
                    result: ResultResponsibility::None,
                    contents: ContentsRelation::NoOldObject,
                },
            ])
        );
    }

    #[test]
    fn e5_r219_dynamic_byte_contract_preserves_direct_branch_cases() {
        let site = one_site(
            "pub unsafe fn dynamic_branch(p: *mut u8, requested: usize) { if requested == 0 { return; } let q = realloc(p, requested); if q.is_null() { free(p); } else { free(q); } }",
        );
        assert_eq!(site.size, ReallocSize::ByteCount);
        assert!(matches!(site.result, ReallocResult::DirectBranch(_)));
        assert_eq!(classify(&site), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r219_dynamic_bytes_do_not_require_an_element_size_fact() {
        let mut collected = sites(
            "unsafe extern \"C\" { fn realloc(p: *mut core::ffi::c_void, requested: usize) -> *mut core::ffi::c_void; } pub unsafe fn byte_contract(p: *mut core::ffi::c_void, requested: usize) -> u8 { let q = realloc(p, requested); *(q as *mut u8) }",
        );
        assert_eq!(collected.len(), 1);
        let site = collected.pop().unwrap();
        assert_eq!(site.size, ReallocSize::ByteCount);
        success_continuation(&site);
        assert_eq!(classify(&site), Ok(vec![nonzero_cases()[0]]));
    }

    #[test]
    fn e5_r219_nonzero_bytes_do_not_require_an_element_size_fact() {
        let mut collected = sites(
            "unsafe extern \"C\" { fn realloc(p: *mut core::ffi::c_void, requested: usize) -> *mut core::ffi::c_void; } pub unsafe fn fixed_bytes(p: *mut core::ffi::c_void) -> u8 { let q = realloc(p, 16); *(q as *mut u8) }",
        );
        assert_eq!(collected.len(), 1);
        let site = collected.pop().unwrap();
        assert_eq!(site.size, ReallocSize::Nonzero);
        success_continuation(&site);
        assert_eq!(classify(&site), Ok(vec![nonzero_cases()[0]]));
    }

    #[test]
    fn e5_r219_absent_byte_contract_and_explicit_zero_remain_typed() {
        let mut site = synthetic_site();
        site.size = ReallocSize::Unknown;
        assert_eq!(classify(&site), Err(ReallocUnsupported::UnknownSize));
        site.size = ReallocSize::Zero;
        assert_eq!(classify(&site), Err(ReallocUnsupported::ZeroSize));
    }

    #[test]
    fn e5_r219_conditional_callee_dereference_is_not_success_evidence() {
        let site = one_site(
            "unsafe fn maybe_read(value: *mut u8, read: bool) -> u8 { if read { *value } else { 0 } } pub unsafe fn conditional_reader(p: *mut u8, read: bool) -> u8 { let q = realloc(p, 16); maybe_read(q, read) }",
        );
        assert!(!matches!(site.result, ReallocResult::SuccessImplied(_)));
        assert_result_test_fallback(&site);
    }

    #[test]
    fn e5_r219_conditional_direct_dereference_is_not_success_evidence() {
        let site = one_site(
            "pub unsafe fn conditional_use(p: *mut u8, read: bool) -> u8 { let q = realloc(p, 16); if read { *q } else { 0 } }",
        );
        assert!(!matches!(site.result, ReallocResult::SuccessImplied(_)));
        assert_result_test_fallback(&site);
    }

    #[test]
    fn e5_r219_opaque_result_control_stays_unsupported() {
        let site = one_site(
            "unsafe extern \"C\" { fn opaque_decision(value: *mut u8) -> bool; } pub unsafe fn opaque_control(p: *mut u8) -> bool { let q = realloc(p, 16); opaque_decision(q) }",
        );
        assert!(!matches!(site.result, ReallocResult::SuccessImplied(_)));
        assert_result_test_fallback(&site);
    }

    fn synthetic_byte_continuation(access_bytes: Option<u64>) -> ReallocSite {
        let mut site = synthetic_site();
        site.size = ReallocSize::ByteCount;
        site.zero_size = Some(ZeroSizeFeasibility::Possible);
        let result = Local::from_u32(2);
        let continuation = ReallocContinuation {
            old: Some(Local::from_u32(1)),
            old_place: Some(PlaceKey {
                local: Local::from_u32(1),
                proj: Vec::new(),
            }),
            result: Some(result),
            result_place: PlaceKey {
                local: result,
                proj: Vec::new(),
            },
            normal: BasicBlock::from_u32(1),
            transports: Vec::new(),
            witness: access_bytes.map(|access_bytes| ReallocUseWitness::DirectDeref {
                location: Location {
                    block: BasicBlock::from_u32(1),
                    statement_index: 0,
                },
                place: PlaceKey {
                    local: result,
                    proj: vec![super::super::export::ProjKey::Deref],
                },
                access_bytes,
            }),
        };
        site.result = if access_bytes.is_some() {
            ReallocResult::SuccessImplied(continuation)
        } else {
            ReallocResult::Unobserved(continuation)
        };
        site
    }

    #[test]
    fn e5_r219_zero_possible_direct_branch_has_zero_size_residual() {
        let mut site = synthetic_site();
        site.size = ReallocSize::ByteCount;
        site.zero_size = Some(ZeroSizeFeasibility::Possible);
        assert_eq!(
            classify(&site),
            Err(ReallocUnsupported::ZeroSize),
            "a byte contract alone cannot promise old storage survives a null result"
        );
    }

    #[test]
    fn e5_r219_zero_guard_does_not_survive_an_address_alias_write() {
        let site = one_site(
            "pub unsafe fn aliased_bytes(p: *mut u8, mut bytes: usize) { let alias = &raw mut bytes; if bytes == 0 { return; } *alias = 0; let q = realloc(p, bytes); if q.is_null() { free(p); } else { free(q); } }",
        );
        assert_eq!(site.size, ReallocSize::ByteCount);
        assert_eq!(
            site.zero_size,
            Some(ZeroSizeFeasibility::Possible),
            "the byte count can change through its address after the nonzero guard"
        );
        assert!(matches!(site.result, ReallocResult::DirectBranch(_)));
        assert_eq!(classify(&site), Err(ReallocUnsupported::ZeroSize));
    }

    #[test]
    fn e5_r219_zero_exclusion_is_carried_from_the_source_guard() {
        let site = one_site(
            "pub unsafe fn guarded_bytes(p: *mut u8, requested: usize) { if requested == 0 { return; } let q = realloc(p, requested); if q.is_null() { free(p); } else { free(q); } }",
        );
        assert!(
            matches!(
                site.zero_size,
                Some(ZeroSizeFeasibility::ExcludedBySourceGuard(_))
            ),
            "the source guard must be evidence, not an assumption from ByteCount"
        );
        assert_eq!(classify(&site), Ok(nonzero_cases()));
    }

    #[test]
    fn e5_r219_zero_unobserved_failure_has_target_dependent_contents() {
        let site = synthetic_byte_continuation(None);
        assert_eq!(
            classify(&site),
            Ok(vec![
                nonzero_cases()[0],
                ReallocCase {
                    outcome: ReallocOutcome::Failure,
                    old: OldResponsibility::LoseClaimIfPresent,
                    result: ResultResponsibility::None,
                    contents: ContentsRelation::TargetDependentZeroSize,
                },
            ])
        );
    }

    #[test]
    fn e5_r219_zero_retirement_availability_is_separate_from_claim_loss() {
        let mut site = synthetic_byte_continuation(None);
        let mut failure = ReallocCase {
            outcome: ReallocOutcome::Failure,
            old: OldResponsibility::LoseClaimIfPresent,
            result: ResultResponsibility::None,
            contents: ContentsRelation::TargetDependentZeroSize,
        };
        assert_eq!(
            retirement_availability(&site, &failure),
            ReallocRetirementAvailability::MayRetireOnZero
        );
        site.size = ReallocSize::Nonzero;
        site.zero_size = None;
        failure.contents = ContentsRelation::OldContentsUnchanged;
        assert_eq!(
            retirement_availability(&site, &failure),
            ReallocRetirementAvailability::None
        );
    }

    #[test]
    fn e5_r219_zero_null_old_has_no_generation_available_to_retire() {
        let mut site = synthetic_byte_continuation(None);
        site.old_input = OldInput::KnownNull;
        let failure = ReallocCase {
            outcome: ReallocOutcome::Failure,
            old: OldResponsibility::Absent,
            result: ResultResponsibility::None,
            contents: ContentsRelation::NoOldObject,
        };
        assert_eq!(
            retirement_availability(&site, &failure),
            ReallocRetirementAvailability::None
        );
    }

    #[test]
    fn e5_r219_zero_byte_deref_is_not_p0_success_evidence() {
        let site = synthetic_byte_continuation(Some(0));
        assert_eq!(
            classify(&site),
            Err(ReallocUnsupported::UnresolvedResultTest)
        );
    }

    #[test]
    fn e5_r219_zero_positive_access_is_required_for_p0_success() {
        let site = synthetic_byte_continuation(Some(1));
        assert_eq!(classify(&site), Ok(vec![nonzero_cases()[0]]));
        assert_eq!(
            retirement_availability(&site, &nonzero_cases()[0]),
            ReallocRetirementAvailability::WholeOldGeneration
        );
    }
}
