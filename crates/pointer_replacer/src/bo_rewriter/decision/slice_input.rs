//! W-C7: slice input propagation.
//!
//! A parameter the fatness analysis already calls an array (`Arr`) but that
//! has no arithmetic of its own — it only forwards its pointer into callee
//! parameters that access past one element — takes the thin `Form::Plain`
//! (the form rule reads the subject's OWN uses) and is then held
//! `held:local-callee-access-extent` (fix-2: a `&T` is a one-element claim and
//! may not be widened at a local callee). When every caller of its function
//! supplies a buffer at that position — an `Arr` subject, or a parameter that
//! is itself supplied this way — the parameter is not a one-element claim but
//! the slice its callers hand it: it takes `&[T]` and the extent travels from
//! the callers as the slice's length. Nothing is widened anywhere: the callers
//! already hold slices, the callees index them with the ordinary bounds check,
//! and a non-array caller anywhere in the closure refuses the whole chain
//! (typed, the hold stays).
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{
    Subject, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts},
    thin_counted,
};
use crate::bo_rewriter::fat_facts::FatFacts;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Proof {
    /// Every function whose parameter the slice travels through, this one
    /// first; each must keep its SliceUse family for the chain to stand.
    pub members: Vec<LocalDefId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Hold {
    OutsideScope,
    /// The subject reaches a callee parameter that is not a buffer.
    CalleeNotFat,
    /// A caller passes something other than a buffer at this position.
    CallerNotSupplied,
    /// Not every caller is known, or one is a fn-pointer / exported entry.
    IncompleteCallers,
}

fn param_index(tcx: TyCtxt<'_>, function: LocalDefId, binding: rustc_hir::HirId) -> Option<usize> {
    tcx.hir_body_owned_by(function)
        .params
        .iter()
        .position(|p| p.pat.hir_id == binding)
}

/// Every position `(function, parameter)` is forwarded into is a fat callee
/// parameter, or a parameter that itself only forwards into fat ones (a
/// forwarder chain); at least one forwarding exists, and a cycle is not fat.
fn forwards_into_fat(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    binding: rustc_hir::HirId,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    visited: &mut Vec<(LocalDefId, usize)>,
) -> Result<(), Hold> {
    let mut forwarded = false;
    for (&callee, calls) in &facts.call_args {
        for call in calls.iter().filter(|call| call.caller == function) {
            for arg in &call.args {
                let ArgShape::BareLocal(argument) = arg.shape else { continue };
                if argument != binding {
                    continue;
                }
                forwarded = true;
                let local = Local::from_usize(arg.index + 1);
                if fat.is_array(callee, local) {
                    continue;
                }
                if visited.contains(&(callee, arg.index)) {
                    return Err(Hold::CalleeNotFat);
                }
                visited.push((callee, arg.index));
                let param = tcx.hir_body_owned_by(callee).params[arg.index].pat.hir_id;
                forwards_into_fat(tcx, callee, param, facts, fat, visited)?;
            }
        }
    }
    if forwarded {
        Ok(())
    } else {
        Err(Hold::CalleeNotFat)
    }
}

fn supplied(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    parameter: usize,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    members: &mut Vec<LocalDefId>,
) -> Result<(), Hold> {
    if members.contains(&function) {
        // A cycle supplies nothing by itself.
        return Err(Hold::CallerNotSupplied);
    }
    members.push(function);
    let calls =
        thin_counted::closed_calls(tcx, function, facts).map_err(|_| Hold::IncompleteCallers)?;
    for call in calls {
        let arg = call
            .args
            .iter()
            .find(|a| a.index == parameter)
            .ok_or(Hold::CallerNotSupplied)?;
        let ArgShape::BareLocal(binding) = arg.shape else {
            return Err(Hold::CallerNotSupplied);
        };
        let Some(index) = param_index(tcx, call.caller, binding) else {
            return Err(Hold::CallerNotSupplied);
        };
        // A supplier is a parameter with array evidence of its OWN — arithmetic
        // uses in its function (the form rule decides it a slice there) — or a
        // forwarder that is itself supplied. The flow-insensitive array verdict
        // alone is not enough: a forwarder carries it from its callees.
        if fat.is_array(call.caller, Local::from_usize(index + 1))
            && facts
                .raw_only_uses
                .get(&(call.caller, binding))
                .is_some_and(|uses| {
                    uses.iter().any(|(op, _)| {
                        super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str())
                    })
                })
        {
            continue;
        }
        supplied(tcx, call.caller, index, facts, fat, members)?;
    }
    Ok(())
}

pub(crate) fn prove(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
) -> Result<Proof, Hold> {
    let SubjectKind::Param { hir_index } = subject.kind else { return Err(Hold::OutsideScope) };
    if subject.ptr_depth != 1 || !fat.is_array(subject.fn_did, subject.local) {
        return Err(Hold::OutsideScope);
    }
    forwards_into_fat(
        tcx,
        subject.fn_did,
        subject.hir_id,
        facts,
        fat,
        &mut vec![(subject.fn_did, hir_index)],
    )?;
    let mut members = Vec::new();
    supplied(tcx, subject.fn_did, hir_index, facts, fat, &mut members)?;
    Ok(Proof { members })
}

pub(crate) fn enabled_proof(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    facts: &EmitabilityFacts,
    fat: &FatFacts,
    policy: &crate::bo_rewriter::additive::FamilyPolicy,
) -> Option<Proof> {
    let proof = prove(tcx, subject, facts, fat).ok()?;
    proof
        .members
        .iter()
        .all(|owner| policy.enabled(*owner, crate::bo_rewriter::additive::FamilyStage::SliceUse))
        .then_some(proof)
}

impl Hold {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::OutsideScope => "outside-scope",
            Self::CalleeNotFat => "callee-not-fat",
            Self::CallerNotSupplied => "caller-not-supplied",
            Self::IncompleteCallers => "incomplete-callers",
        }
    }
}
