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
    /// Where the slice's extent comes from.
    pub extent: Extent,
}

/// R418-1 (relay 024): the forwarder's extent is evidence-backed only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Extent {
    /// Every caller supplies a slice (W-C7) or a fresh root (W-C9): the
    /// extent travels down as the slice's length.
    Supplied,
    /// The forwarder's OWN companion integer beside the pointer
    /// (`adler32(data, len)`): its callers adapt raw with it, or take the
    /// slice form themselves, or decline typed (`thin-caller-argument`).
    Companion(super::seam::LenEvidence),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Hold {
    OutsideScope,
    /// The subject reaches a callee parameter that is not a buffer.
    CalleeNotFat,
    /// A caller passes something other than a binding at this position (a
    /// computed pointer, an address, a cast).
    CallerNotSupplied,
    /// A caller's binding at this position is null-tested: its own form is
    /// the thin Option, which the extent hold does not reach.
    CallerNullable,
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
        let uses = facts.raw_only_uses.get(&(call.caller, binding));
        let has = |op: &str| uses.is_some_and(|uses| uses.iter().any(|(use_op, _)| use_op == op));
        if let Some(index) = param_index(tcx, call.caller, binding) {
            // A supplier is a parameter with array evidence of its OWN —
            // arithmetic uses in its function (the form rule decides it a
            // slice there) — or a forwarder that is itself supplied. The
            // flow-insensitive array verdict alone is not enough: a forwarder
            // carries it from its callees.
            if fat.is_array(call.caller, Local::from_usize(index + 1))
                && uses.is_some_and(|uses| {
                    uses.iter().any(|(op, _)| {
                        super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str())
                    })
                })
            {
                continue;
            }
            let reached = members.len();
            match supplied(tcx, call.caller, index, facts, fat, members) {
                Ok(()) => continue,
                Err(Hold::IncompleteCallers | Hold::CallerNotSupplied | Hold::CallerNullable) => {
                    members.truncate(reached);
                }
                Err(hold) => return Err(hold),
            }
        }
        // **W-C9 — a fresh root supplies the chain.** The caller's own
        // allocation local (`BrotliSplitBlock::literals`): a binding whose
        // every definition is a call that takes no pointer — so its value is
        // a fresh allocation, never a borrow of anything thinner — or the
        // null literal. Such a binding never takes the thin form (a fresh
        // pointer has no referent to be a one-element claim on); it is
        // either owning or stays raw, and the call then takes the
        // companion-length adapter — the seam every raw caller of a slice
        // parameter already takes. A null-TESTED root is the thin Option,
        // which no extent hold reaches, so it refuses; anything else that
        // is not a fresh root (a parameter whose own callers refused, a
        // pointer read out of a field) refuses as before.
        if has("is_null") {
            return Err(Hold::CallerNullable);
        }
        if param_index(tcx, call.caller, binding).is_some()
            || !fresh_root(tcx, call.caller, binding)
        {
            return Err(Hold::CallerNotSupplied);
        }
    }
    Ok(())
}

/// A call whose arguments carry no pointer: what it returns was made by the
/// callee, not borrowed from the caller (`xalloc(n)`, `malloc(n)`). Brotli's
/// `BrotliAllocate(m, n)` takes its memory manager and is NOT this shape;
/// it is the allocator contract's (R409-1, wave-6a's consumer).
fn fresh_call(tcx: TyCtxt<'_>, owner: LocalDefId, e: &rustc_hir::Expr<'_>) -> bool {
    use rustc_hir::ExprKind;
    let types = tcx.typeck(owner);
    match e.kind {
        ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) => fresh_call(tcx, owner, inner),
        ExprKind::Block(block, _) => match (block.stmts, block.expr) {
            ([], Some(tail)) => fresh_call(tcx, owner, tail),
            _ => false,
        },
        ExprKind::If(_, then, Some(otherwise)) => {
            // `if n > 0 { alloc(n) } else { null }`: one arm allocates, the
            // other may be the null literal; two null arms allocate nothing.
            let then_fresh = fresh_call(tcx, owner, then);
            let otherwise_fresh = fresh_call(tcx, owner, otherwise);
            (then_fresh || otherwise_fresh)
                && (then_fresh || super::emitability::is_zero_literal(then))
                && (otherwise_fresh || super::emitability::is_zero_literal(otherwise))
        }
        ExprKind::Call(_, args) => args.iter().all(|arg| !types.expr_ty(arg).is_any_ptr()),
        _ => false,
    }
}

fn fresh_root(tcx: TyCtxt<'_>, owner: LocalDefId, binding: rustc_hir::HirId) -> bool {
    use rustc_hir::{
        ExprKind, Node,
        def::Res,
        intravisit::{self, Visitor},
    };
    let Node::LetStmt(stmt) = tcx.parent_hir_node(binding) else { return false };
    let Some(init) = stmt.init else { return false };
    if !fresh_call(tcx, owner, init) {
        return false;
    }
    struct Assigned<'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        binding: rustc_hir::HirId,
        refused: bool,
    }
    impl<'tcx> Visitor<'tcx> for Assigned<'tcx> {
        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = e.kind
                && let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = lhs.kind
                && path.res == Res::Local(self.binding)
                && !(fresh_call(self.tcx, self.owner, rhs)
                    || super::emitability::is_zero_literal(rhs))
            {
                self.refused = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut assigned = Assigned {
        tcx,
        owner,
        binding,
        refused: false,
    };
    assigned.visit_body(tcx.hir_body_owned_by(owner));
    !assigned.refused
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
    match supplied(tcx, subject.fn_did, hir_index, facts, fat, &mut members) {
        Ok(()) => Ok(Proof {
            members,
            extent: Extent::Supplied,
        }),
        // The signature must still be this crate's to change.
        Err(Hold::IncompleteCallers) => Err(Hold::IncompleteCallers),
        Err(hold) => {
            // **The companion may not overrule measured count evidence.** The
            // thin-count rule reads every caller's count against the array it
            // passes; when that read HOLDS on the count itself
            // (`caller-count`: a constant that does not fit the capacity, or a
            // foldable one out of range), the adjacent integer is exactly the
            // number this lane has already refused as an extent. Taking it
            // here would put `from_raw_parts(a.as_ptr(), 19)` on an
            // 18-element array — out of the addendum-77 waiver and into
            // ordinary out-of-bounds UB.
            if matches!(
                thin_counted::prove(tcx, subject, facts),
                Err(thin_counted::Hold::CallerCount)
            ) {
                return Err(hold);
            }
            let evidence = super::seam::length_evidence(tcx, subject.fn_did, hir_index);
            if matches!(
                evidence,
                super::seam::LenEvidence::Following | super::seam::LenEvidence::Preceding
            ) {
                Ok(Proof {
                    members: vec![subject.fn_did],
                    extent: Extent::Companion(evidence),
                })
            } else {
                Err(hold)
            }
        }
    }
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
            Self::CallerNullable => "caller-nullable",
            Self::IncompleteCallers => "incomplete-callers",
        }
    }
}
