//! **R464-3 — the compare-only offset fact.**
//!
//! `offset_sign`'s export is two-valued: `Neg` and `Top` share one bit
//! (S3.2′-3), so a pointer whose sign cannot be bounded is refused the plain
//! and optional slice forms alike. binn's header readers are refused by that
//! bit while being, in fact, forward-only walks: of the nine offset-like calls
//! in `IsValidBinnHeader`, five advance the cursor that is read and all five
//! take a non-negative literal, while the three non-literal ones
//! (`plimit = p.offset(*psize - 1)`, two `p.offset(size_of::<c_int>() - 1)`)
//! produce values that are only COMPARED — never dereferenced, stored,
//! returned or passed.
//!
//! **The discriminating fact is the result's use, not the operand's sign.** A
//! value that is only compared does not move the window that is read: whatever
//! its sign, nothing is accessed through it. So the guard may be admitted when
//! every offset whose operand is not a non-negative literal produces such a
//! value, and every offset that DOES move the read window takes a non-negative
//! literal.
//!
//! Decision-side by construction (R320-1): this reads MIR of the owner
//! function and never touches `analyses/offset_sign`, whose export is
//! unchanged. A variable advancing offset keeps the refusal — the 24 corpus
//! rows of report 027 stay refused, correctly.
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BinOp, Body, Local, Operand, Place, PlaceElem, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

/// The offset-like methods a c2rust cursor walk uses.
const OFFSET_OPS: &[&str] = &[
    "offset",
    "add",
    "sub",
    "wrapping_offset",
    "wrapping_add",
    "wrapping_sub",
];

/// Why the fact refuses, for the receipt and the witnesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Refusal {
    /// An offset whose operand is not a non-negative literal produces a value
    /// the body then READS THROUGH (dereferences, stores, returns, passes).
    AdvancingNonLiteral { callee: String },
}

/// Does every offset-like call on this subject's chain either take a
/// non-negative literal, or produce a value that is only compared?
///
/// `false` for a body this walk cannot read (no MIR), which is the
/// conservative side: the guard keeps its refusal.
pub(crate) fn every_advancing_offset_is_a_non_negative_literal(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    subject: Local,
) -> Result<(), Refusal> {
    if !tcx.is_mir_available(function.to_def_id()) {
        return Err(Refusal::AdvancingNonLiteral {
            callee: "<mir-unavailable>".to_owned(),
        });
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let chain = alias_closure(body, subject);
    for data in body.basic_blocks.iter() {
        let Some(terminator) = &data.terminator else { continue };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let Some(name) = offset_op(tcx, func) else { continue };
        let [receiver, operand] = &args[..] else { continue };
        let Some(receiver) = operand_local(&receiver.node) else { continue };
        if !chain.contains(&receiver) {
            continue;
        }
        if non_negative_literal(&operand.node) {
            // A forward step by a literal. It may advance freely.
            continue;
        }
        let Some(result) = destination.as_local() else {
            return Err(Refusal::AdvancingNonLiteral { callee: name });
        };
        if advances(tcx, body, result) {
            return Err(Refusal::AdvancingNonLiteral { callee: name });
        }
    }
    Ok(())
}

fn offset_op(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<String> {
    let path = callee_path(tcx, func)?;
    let last = path.rsplit("::").next()?;
    OFFSET_OPS.contains(&last).then(|| path.clone())
}

fn callee_path(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<String> {
    let ty = func.constant()?.const_.ty();
    let rustc_middle::ty::TyKind::FnDef(did, _) = ty.kind() else { return None };
    Some(tcx.def_path_str(*did))
}

fn callee_name(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<String> {
    Some(callee_path(tcx, func)?.rsplit("::").next()?.to_owned())
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}

/// A literal `0`, `1`, `4`, … — the operand's own sign, read off the constant.
/// A negated literal is `Neg(const)` in MIR and is therefore NOT a constant
/// operand, so it lands on the non-literal side and is judged by its use.
fn non_negative_literal(operand: &Operand<'_>) -> bool {
    let Some(constant) = operand.constant() else { return false };
    let Some(scalar) = constant.const_.try_to_scalar_int() else { return false };
    scalar.to_int(scalar.size()) >= 0
}

/// Copies and casts of a local, plus a raw pointer taken THROUGH one
/// (`&*p` / `p as *const u8`), which point at the same place.
fn alias_closure(body: &Body<'_>, start: Local) -> FxHashSet<Local> {
    let mut closure = FxHashSet::from_iter([start]);
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = (&assignment.0, &assignment.1);
                let source = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_local(operand),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        matches!(place.projection.first(), Some(PlaceElem::Deref))
                            .then_some(place.local)
                    }
                    _ => None,
                };
                if let Some(source) = source
                    && closure.contains(&source)
                    && let Some(destination) = lhs.as_local()
                    && closure.insert(destination)
                {
                    changed = true;
                }
            }
        }
    }
    closure
}

/// Does this offset RESULT move a window the body reads — or is it only
/// compared?
///
/// Conservative in both directions that matter: an alias of the result that is
/// dereferenced, written through, passed to a call, returned, or stored into a
/// place advances; only comparison operands (and the `StorageLive`/`Dead`
/// bookkeeping around them) do not.
fn advances(tcx: TyCtxt<'_>, body: &Body<'_>, result: Local) -> bool {
    let closure = alias_closure(body, result);
    let touches = |place: &Place<'_>| closure.contains(&place.local);
    let through_deref =
        |place: &Place<'_>| touches(place) && place.projection.contains(&PlaceElem::Deref);
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (lhs, rhs) = (&assignment.0, &assignment.1);
            // Written THROUGH the result, or stored into a place that is not
            // itself part of the closure (an escape).
            if through_deref(lhs) {
                return true;
            }
            match rhs {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                    if let Operand::Copy(place) | Operand::Move(place) = operand {
                        if through_deref(place) {
                            return true;
                        }
                        if touches(place) && lhs.as_local().is_none() {
                            return true;
                        }
                    }
                }
                Rvalue::BinaryOp(op, operands) => {
                    let comparison = matches!(
                        op,
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                    );
                    for operand in [&operands.0, &operands.1] {
                        if let Operand::Copy(place) | Operand::Move(place) = operand
                            && touches(place)
                            && !comparison
                        {
                            return true;
                        }
                    }
                }
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    if touches(place) && !matches!(place.projection.first(), Some(PlaceElem::Deref))
                    {
                        return true;
                    }
                    if through_deref(place) {
                        return true;
                    }
                }
                Rvalue::Aggregate(_, operands) => {
                    for operand in operands.iter() {
                        if let Operand::Copy(place) | Operand::Move(place) = operand
                            && touches(place)
                        {
                            return true;
                        }
                    }
                }
                _ => {}
            }
        }
        let Some(terminator) = &data.terminator else { continue };
        match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => {
                // An offset-like call ON the result keeps the chain (the walk
                // continues); any other call PASSES it out of this body.
                let offset_like = offset_op(tcx, func).is_some();
                // A NULL TEST reads the value and nothing through it — the
                // relay's own pairing ("compared / null-tested only"). It is
                // how a c2rust header walk asks whether the limit exists.
                if callee_name(tcx, func).as_deref() == Some("is_null") {
                    continue;
                }
                for (index, argument) in args.iter().enumerate() {
                    if let Operand::Copy(place) | Operand::Move(place) = &argument.node
                        && touches(place)
                    {
                        if offset_like && index == 0 {
                            continue;
                        }
                        return true;
                    }
                }
            }
            TerminatorKind::Return => {
                if closure.contains(&Local::from_usize(0)) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}
